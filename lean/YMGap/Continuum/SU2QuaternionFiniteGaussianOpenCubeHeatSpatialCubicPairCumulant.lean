/-
# Complete heat-normalized spatial cubic-pair cumulant

The complete second density contains `V3^2/2`, where `V3` is the sum of the
exact `H3/4` action coefficient over every internal spatial face and every
history slice.  This leaf rebuilds that complete ordered half-square on the
heat-normalized `(2L)^{-1}` rows and reduces its connected insertion against
the actual trace-source quadratics `A2(left), A2(right)` to the existing
finite `2+2+6` Wick compiler.

Every cross-face and cross-time ordered pair is retained.  The result is a
finite FREE coefficient only; it proves no sign, ORIGINAL-law comparison,
higher-remainder estimate, continuum theory, or physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients

local infix:50 " ≈ " => Q'.eqv

private theorem weightedTermPolynomial_append
    (left right : List (Q' × RatPoly)) :
    RatPolyCoeffEqv
      (polyAdd (weightedTermPolynomial left) (weightedTermPolynomial right))
      (weightedTermPolynomial (left ++ right)) := by
  unfold weightedTermPolynomial
  simpa only [List.map_append] using
    RatPolyCoeffEqv.polySum_append
      (left.map fun term => polySmul term.1 term.2)
      (right.map fun term => polySmul term.1 term.2)

private theorem weightedTermPolynomial_flatMap {Index : Type}
    (block : Index → List (Q' × RatPoly)) : ∀ items : List Index,
    RatPolyCoeffEqv
      (polySum (items.map fun item => weightedTermPolynomial (block item)))
      (weightedTermPolynomial (items.flatMap block))
  | [] => RatPolyCoeffEqv.refl _
  | item :: items =>
      ((RatPolyCoeffEqv.refl _).add
        (weightedTermPolynomial_flatMap block items)).trans
      (weightedTermPolynomial_append (block item) (items.flatMap block))

/-- Complete heat-normalized spatial cubic row blocks. -/
def completeOpenCubeHeatSpatialCubicRowBlocks
    (timeBonds width stage : Nat) : List WeightedCubicRowBlock :=
  (completeOpenCubeSpatialCubicSites timeBonds width).flatMap fun site =>
    openCubeHeatPlaquetteSpatialCubicRowBlocks
      timeBonds width stage site.1 site.2

/-- Literal complete heat-normalized spatial cubic action `V3`. -/
def completeOpenCubeHeatSpatialCubicPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeSpatialCubicSites timeBonds width).map fun site =>
    openCubeHeatPlaquetteSpatialCubicPolynomial
      timeBonds width stage site.1 site.2)

theorem completeOpenCubeHeatSpatialCubicPolynomial_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeHeatSpatialCubicPolynomial
        timeBonds width stage)
      (weightedTermPolynomial
        ((completeOpenCubeHeatSpatialCubicRowBlocks
          timeBonds width stage).map
            (weightedCubicRowBlockTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  let noiseCount := combGaugePlaquetteNoiseCount timeBonds width
  let sites := completeOpenCubeSpatialCubicSites timeBonds width
  let blocks := fun site : Nat × Z4Plaq =>
    openCubeHeatPlaquetteSpatialCubicRowBlocks
      timeBonds width stage site.1 site.2
  have hflat := weightedTermPolynomial_flatMap
    (fun site => (blocks site).map
      (weightedCubicRowBlockTerm noiseCount)) sites
  unfold completeOpenCubeHeatSpatialCubicPolynomial
    openCubeHeatPlaquetteSpatialCubicPolynomial
    finiteGaussianCayleySpatialCubicPolynomial
    completeOpenCubeHeatSpatialCubicRowBlocks
    openCubeHeatPlaquetteSpatialCubicRowBlocks
  change RatPolyCoeffEqv
    (polySum (sites.map fun site =>
      weightedTermPolynomial
        ((blocks site).map (weightedCubicRowBlockTerm noiseCount))))
    (weightedTermPolynomial
      ((sites.flatMap blocks).map
        (weightedCubicRowBlockTerm noiseCount)))
  simpa only [List.map_flatMap] using hflat

/-- Complete ordered heat-normalized half-square `V3^2/2`. -/
def completeOpenCubeHeatSpatialCubicPairPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  let cubic := completeOpenCubeHeatSpatialCubicPolynomial
    timeBonds width stage
  polySmul cubicPairHalf (polyMul cubic cubic)

/-- Complete ordered sextic row blocks of heat-normalized `V3^2/2`. -/
def completeOpenCubeHeatSpatialCubicPairSexticRowBlocks
    (timeBonds width stage : Nat) : List WeightedSexticRowBlock :=
  let cubicBlocks := completeOpenCubeHeatSpatialCubicRowBlocks
    timeBonds width stage
  finiteGaussianCubicPairSexticRowBlocks cubicBlocks cubicBlocks

theorem completeOpenCubeHeatSpatialCubicPairPolynomial_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeHeatSpatialCubicPairPolynomial
        timeBonds width stage)
      (weightedTermPolynomial
        ((completeOpenCubeHeatSpatialCubicPairSexticRowBlocks
          timeBonds width stage).map
            (weightedSexticRowBlockTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  let noiseCount := combGaugePlaquetteNoiseCount timeBonds width
  let cubicBlocks := completeOpenCubeHeatSpatialCubicRowBlocks
    timeBonds width stage
  have hcubic := completeOpenCubeHeatSpatialCubicPolynomial_coeffEqv
    timeBonds width stage
  have hsquare := (hcubic.mul hcubic).smul cubicPairHalf
  have hpairs := finiteGaussianCubicPairPolynomial_coeffEqv
    noiseCount cubicBlocks cubicBlocks
  unfold completeOpenCubeHeatSpatialCubicPairPolynomial
    completeOpenCubeHeatSpatialCubicPairSexticRowBlocks
  exact hsquare.trans hpairs

/-- Explicit Wick sum for actual heat-normalized trace-source quadratics and
the complete ordered cubic half-square. -/
def openCubeHeatCayleyTraceCompleteSpatialCubicPairWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedSexticRowBlocksWickSum
    (bulkSourceNoiseCount timeBonds side)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage leftTime)
    (openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage rightTime)
    (completeOpenCubeHeatSpatialCubicPairSexticRowBlocks
      timeBonds (bulkSourceWidth side) stage)

/-- The actual heat-normalized `A2,A2,V3^2/2` connected insertion is exactly
the displayed finite weighted `2+2+6` Wick sum. -/
theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_completeSpatialCubicPair_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatSpatialCubicPairPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceCompleteSpatialCubicPairWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  let insertionBlocks := completeOpenCubeHeatSpatialCubicPairSexticRowBlocks
    timeBonds (bulkSourceWidth side) stage
  have hnoise : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) = noiseCount := by
    unfold combGaugePlaquetteNoiseCount noiseCount bulkSourceNoiseCount
    rfl
  have hleft := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage leftTime
  have hright := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage rightTime
  have hinsertion := completeOpenCubeHeatSpatialCubicPairPolynomial_coeffEqv
    timeBonds (bulkSourceWidth side) stage
  rw [hnoise] at hinsertion
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_coeffEqv noiseCount
      hleft hright hinsertion)
    (finiteGaussianThirdCumulant_weighted_sextic_row_blocks_wick
      noiseCount leftBlocks rightBlocks insertionBlocks)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant.completeOpenCubeHeatSpatialCubicPolynomial_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant.completeOpenCubeHeatSpatialCubicPairPolynomial_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant.finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_completeSpatialCubicPair_wick
