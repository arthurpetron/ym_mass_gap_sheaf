/-
# Heat-normalized fourth-action and Cayley-Haar cumulants

This leaf migrates the remaining homogeneous components of the complete
second density to the corrected `(2L)^{-1}` heat rows.  It constructs the
complete spatial fourth-action quartic and quadratic block families, the
complete kinetic fourth-action quartic and quadratic families, and the
complete product-Cayley Haar `J2` row-square family.  Each connected insertion
against the actual heat-normalized trace-source quadratics `A2(left),A2(right)`
is reduced to the existing finite Wick compiler.

The component polynomials are literal weighted-term polynomials of the exact
Cayley and kinetic blocks.  This file does not yet assemble their density
signs with `V3^2/2`, rebuild the full order-six response, compare the ORIGINAL
law, or prove a continuum theory or physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatSpatialCubicPairCumulant
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatFourthActionHaarCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCompleteSecondDensityCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients

local infix:50 " ≈ " => Q'.eqv

private theorem polySum_congr {Index : Type}
    (left right : Index → RatPoly) : ∀ items : List Index,
    (∀ item, item ∈ items → RatPolyCoeffEqv (left item) (right item)) →
    RatPolyCoeffEqv (polySum (items.map left)) (polySum (items.map right))
  | [], _ => RatPolyCoeffEqv.refl _
  | item :: items, h =>
      (h item List.mem_cons_self).add
        (polySum_congr left right items
          (fun other hother => h other (List.mem_cons_of_mem item hother)))

/-- Scale a weighted row square while retaining its row. -/
def scaleHeatWeightedRowSquare
    (scale : Q') (square : WeightedRowSquare) : WeightedRowSquare :=
  { weight := scale * square.weight
    row := square.row }

/-- Complete quartic blocks of one heat-normalized spatial `V4` face. -/
def openCubeHeatSpatialFourthActionQuarticRowBlocks
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedQuarticRowBlock :=
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  (finiteGaussianNormalizedCayleyH4QuarticRowBlocks
    (rows 0) (rows 1) (rows 2) (rows 3)).map
      (scaleWeightedQuarticRowBlock spatialHeatQuarter) ++
    finiteGaussianCayleyH2SquareActionRowBlocks
      (rows 0) (rows 1) (rows 2) (rows 3)

/-- Complete quadratic row squares of one heat-normalized spatial `V4` face. -/
def openCubeHeatSpatialFourthActionQuadraticRowSquares
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedRowSquare :=
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianCayleyH2ActionRowSquares
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Complete heat-normalized spatial `V4` quartic blocks. -/
def completeOpenCubeHeatSpatialFourthActionQuarticRowBlocks
    (timeBonds width stage : Nat) : List WeightedQuarticRowBlock :=
  (completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width).flatMap fun insertion =>
      (openCubeHeatSpatialFourthActionQuarticRowBlocks
        timeBonds width stage insertion.time insertion.face).map
          (scaleWeightedQuarticRowBlock insertion.weight)

/-- Complete heat-normalized spatial `V4` quadratic row squares. -/
def completeOpenCubeHeatSpatialFourthActionQuadraticRowSquares
    (timeBonds width stage : Nat) : List WeightedRowSquare :=
  (completeOpenCubeSpatialHeatActionFourthInsertions
    timeBonds width).flatMap fun insertion =>
      (openCubeHeatSpatialFourthActionQuadraticRowSquares
        timeBonds width stage insertion.time insertion.face).map
          (scaleHeatWeightedRowSquare insertion.weight)

/-- Literal complete spatial `V4` on the corrected heat rows. -/
def completeOpenCubeHeatSpatialFourthActionPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  let noiseCount := combGaugePlaquetteNoiseCount timeBonds width
  polyAdd
    (weightedTermPolynomial
      ((completeOpenCubeHeatSpatialFourthActionQuarticRowBlocks
        timeBonds width stage).map
          (weightedQuarticRowBlockTerm noiseCount)))
    (weightedTermPolynomial
      ((completeOpenCubeHeatSpatialFourthActionQuadraticRowSquares
        timeBonds width stage).map
          (weightedRowSquareTerm noiseCount)))

/-- Quartic blocks of one heat-normalized kinetic `V4` insertion. -/
def openCubeHeatKineticFourthActionQuarticRowBlocks
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    List WeightedQuarticRowBlock :=
  finiteGaussianKineticFourthActionQuarticRowBlocks
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)

/-- Quadratic row squares of one heat-normalized kinetic `V4` insertion. -/
def openCubeHeatKineticFourthActionQuadraticRowSquares
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    List WeightedRowSquare :=
  finiteGaussianKineticFourthActionQuadraticRowSquares
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)

/-- Complete heat-normalized kinetic `V4` quartic blocks. -/
def completeOpenCubeHeatKineticFourthActionQuarticRowBlocks
    (timeBonds width stage : Nat) : List WeightedQuarticRowBlock :=
  (completeOpenCubeKineticFourthActionInsertions
    timeBonds width).flatMap fun insertion =>
      (openCubeHeatKineticFourthActionQuarticRowBlocks
        timeBonds width stage insertion.bond insertion.link).map
          (scaleWeightedQuarticRowBlock insertion.weight)

/-- Complete heat-normalized kinetic `V4` quadratic row squares. -/
def completeOpenCubeHeatKineticFourthActionQuadraticRowSquares
    (timeBonds width stage : Nat) : List WeightedRowSquare :=
  (completeOpenCubeKineticFourthActionInsertions
    timeBonds width).flatMap fun insertion =>
      (openCubeHeatKineticFourthActionQuadraticRowSquares
        timeBonds width stage insertion.bond insertion.link).map
          (scaleHeatWeightedRowSquare insertion.weight)

/-- Literal complete kinetic `V4` on the corrected heat rows. -/
def completeOpenCubeHeatKineticFourthActionPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  let noiseCount := combGaugePlaquetteNoiseCount timeBonds width
  polyAdd
    (weightedTermPolynomial
      ((completeOpenCubeHeatKineticFourthActionQuarticRowBlocks
        timeBonds width stage).map
          (weightedQuarticRowBlockTerm noiseCount)))
    (weightedTermPolynomial
      ((completeOpenCubeHeatKineticFourthActionQuadraticRowSquares
        timeBonds width stage).map
          (weightedRowSquareTerm noiseCount)))

/-- Local heat-normalized Cayley-Haar `J2` row squares. -/
def openCubeHeatCayleyHaarJ2RowSquares
    (timeBonds width stage time : Nat) (link : Z4Link) :
    List WeightedRowSquare :=
  finiteGaussianCayleyHaarJ2RowSquares
    (combGaugeHeatFreeHistoryHeronKineticSliceRows
      timeBonds width stage time link)

/-- Complete heat-normalized Cayley-Haar `J2` row squares. -/
def completeOpenCubeHeatCayleyHaarJ2RowSquares
    (timeBonds width stage : Nat) : List WeightedRowSquare :=
  (completeOpenCubeCayleyHaarJ2Insertions
    timeBonds width).flatMap fun insertion =>
      (openCubeHeatCayleyHaarJ2RowSquares
        timeBonds width stage insertion.time insertion.link).map
          (scaleHeatWeightedRowSquare insertion.weight)

/-- Literal complete product-Cayley Haar `J2` on the corrected heat rows. -/
def completeOpenCubeHeatCayleyHaarJ2Polynomial
    (timeBonds width stage : Nat) : RatPoly :=
  weightedTermPolynomial
    ((completeOpenCubeHeatCayleyHaarJ2RowSquares
      timeBonds width stage).map
        (weightedRowSquareTerm
          (combGaugePlaquetteNoiseCount timeBonds width)))

/-- Explicit connected value of the complete spatial `V4`. -/
def openCubeHeatCayleyTraceSpatialFourthActionWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  let quarticBlocks := completeOpenCubeHeatSpatialFourthActionQuarticRowBlocks
    timeBonds (bulkSourceWidth side) stage
  let quadraticSquares :=
    completeOpenCubeHeatSpatialFourthActionQuadraticRowSquares
      timeBonds (bulkSourceWidth side) stage
  finiteGaussianWeightedRowBlocksWickSum
      noiseCount leftBlocks rightBlocks quarticBlocks +
    finiteGaussianWeightedRowSquaresTriangleSum
      noiseCount
      (leftBlocks.map fun block =>
        { weight := block.weight, row := block.first })
      (rightBlocks.map fun block =>
        { weight := block.weight, row := block.first })
      quadraticSquares

private def quadraticBlocksToSquares
    (blocks : List WeightedQuadraticRowBlock) : List WeightedRowSquare :=
  blocks.map fun block => { weight := block.weight, row := block.first }

private theorem quadraticBlocksToSquares_polynomial
    (noiseCount : Nat) (blocks : List WeightedQuadraticRowBlock)
    (diagonal : ∀ block, block ∈ blocks → block.first = block.second) :
    RatPolyCoeffEqv
      (weightedTermPolynomial
        (blocks.map (weightedQuadraticRowBlockTerm noiseCount)))
      (weightedTermPolynomial
        ((quadraticBlocksToSquares blocks).map
          (weightedRowSquareTerm noiseCount))) := by
  unfold quadraticBlocksToSquares weightedTermPolynomial
    weightedQuadraticRowBlockTerm weightedRowSquareTerm
    finiteGaussianRowSquare finiteGaussianRowWord
  simp only [List.map_map]
  exact polySum_congr _ _ blocks (fun block hblock => by
    change RatPolyCoeffEqv
      (polySmul block.weight
        (polyMul (finiteLinearRow noiseCount block.first)
          (finiteLinearRow noiseCount block.second)))
      (polySmul block.weight
        (polyMul (finiteLinearRow noiseCount block.first)
          (finiteLinearRow noiseCount block.first)))
    rw [← diagonal block hblock]
    exact RatPolyCoeffEqv.refl _)

private theorem heatA2Blocks_diagonal
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) (block : WeightedQuadraticRowBlock)
    (membership : block ∈ openCubeHeatBulkCayleyTraceA2RowBlocks
      timeBonds side sidePositive stage time) :
    block.first = block.second := by
  unfold openCubeHeatBulkCayleyTraceA2RowBlocks at membership
  simp only [List.mem_map] at membership
  rcases membership with ⟨base, hbase, rfl⟩
  unfold bulkSourceHeatQuadraticRowBlocks at hbase
  simp only [List.mem_map] at hbase
  rcases hbase with ⟨rowIndex, _hrowIndex, rfl⟩
  rfl

private theorem finiteGaussianThirdCumulant_quartic_quadratic_wick
    (noiseCount : Nat) (left right : RatPoly)
    (leftBlocks rightBlocks : List WeightedQuadraticRowBlock)
    (quarticBlocks : List WeightedQuarticRowBlock)
    (quadraticSquares : List WeightedRowSquare)
    (hleftBlocks : RatPolyCoeffEqv left
      (weightedTermPolynomial
        (leftBlocks.map (weightedQuadraticRowBlockTerm noiseCount))))
    (hrightBlocks : RatPolyCoeffEqv right
      (weightedTermPolynomial
        (rightBlocks.map (weightedQuadraticRowBlockTerm noiseCount))))
    (hleftSquares : RatPolyCoeffEqv left
      (weightedTermPolynomial
        ((quadraticBlocksToSquares leftBlocks).map
          (weightedRowSquareTerm noiseCount))))
    (hrightSquares : RatPolyCoeffEqv right
      (weightedTermPolynomial
        ((quadraticBlocksToSquares rightBlocks).map
          (weightedRowSquareTerm noiseCount)))) :
    finiteGaussianThirdCumulant noiseCount left right
        (polyAdd
          (weightedTermPolynomial
            (quarticBlocks.map (weightedQuarticRowBlockTerm noiseCount)))
          (weightedTermPolynomial
            (quadraticSquares.map (weightedRowSquareTerm noiseCount)))) ≈
      finiteGaussianWeightedRowBlocksWickSum
          noiseCount leftBlocks rightBlocks quarticBlocks +
        finiteGaussianWeightedRowSquaresTriangleSum
          noiseCount
          (quadraticBlocksToSquares leftBlocks)
          (quadraticBlocksToSquares rightBlocks)
          quadraticSquares := by
  have hsource := finiteGaussianThirdCumulant_coeffEqv noiseCount
    hleftBlocks hrightBlocks
      (RatPolyCoeffEqv.refl
        (polyAdd
          (weightedTermPolynomial
            (quarticBlocks.map (weightedQuarticRowBlockTerm noiseCount)))
          (weightedTermPolynomial
            (quadraticSquares.map (weightedRowSquareTerm noiseCount)))))
  have hadd := finiteGaussianThirdCumulant_add_right noiseCount
    (weightedTermPolynomial
      (leftBlocks.map (weightedQuadraticRowBlockTerm noiseCount)))
    (weightedTermPolynomial
      (rightBlocks.map (weightedQuadraticRowBlockTerm noiseCount)))
    (weightedTermPolynomial
      (quarticBlocks.map (weightedQuarticRowBlockTerm noiseCount)))
    (weightedTermPolynomial
      (quadraticSquares.map (weightedRowSquareTerm noiseCount)))
  have hquartic := finiteGaussianThirdCumulant_weighted_row_blocks_wick
    noiseCount leftBlocks rightBlocks quarticBlocks
  have hleftBlockSquares := hleftBlocks.symm.trans hleftSquares
  have hrightBlockSquares := hrightBlocks.symm.trans hrightSquares
  have hquadraticCongr := finiteGaussianThirdCumulant_coeffEqv noiseCount
    hleftBlockSquares hrightBlockSquares
      (RatPolyCoeffEqv.refl
        (weightedTermPolynomial
          (quadraticSquares.map (weightedRowSquareTerm noiseCount))))
  have hquadratic := finiteGaussianThirdCumulant_weighted_row_squares_triangle
    noiseCount (quadraticBlocksToSquares leftBlocks)
      (quadraticBlocksToSquares rightBlocks) quadraticSquares
  exact Q'.eqv_trans _ _ _ hsource
    (Q'.eqv_trans _ _ _ hadd
      (Q'.add_eqv_congr' hquartic
        (Q'.eqv_trans _ _ _ hquadraticCongr hquadratic)))

private theorem finiteGaussianThirdCumulant_row_squares_triangle
    (noiseCount : Nat) (left right : RatPoly)
    (leftSquares rightSquares insertionSquares : List WeightedRowSquare)
    (hleft : RatPolyCoeffEqv left
      (weightedTermPolynomial
        (leftSquares.map (weightedRowSquareTerm noiseCount))))
    (hright : RatPolyCoeffEqv right
      (weightedTermPolynomial
        (rightSquares.map (weightedRowSquareTerm noiseCount)))) :
    finiteGaussianThirdCumulant noiseCount left right
        (weightedTermPolynomial
          (insertionSquares.map (weightedRowSquareTerm noiseCount))) ≈
      finiteGaussianWeightedRowSquaresTriangleSum noiseCount
        leftSquares rightSquares insertionSquares := by
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_coeffEqv noiseCount hleft hright
      (RatPolyCoeffEqv.refl
        (weightedTermPolynomial
          (insertionSquares.map (weightedRowSquareTerm noiseCount)))))
    (finiteGaussianThirdCumulant_weighted_row_squares_triangle
      noiseCount leftSquares rightSquares insertionSquares)

theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_spatialFourthAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatSpatialFourthActionPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceSpatialFourthActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  have hleftBlocks := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage leftTime
  have hrightBlocks := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage rightTime
  have hleftSquares := hleftBlocks.trans
    (quadraticBlocksToSquares_polynomial noiseCount leftBlocks
      (heatA2Blocks_diagonal timeBonds side sidePositive stage leftTime))
  have hrightSquares := hrightBlocks.trans
    (quadraticBlocksToSquares_polynomial noiseCount rightBlocks
      (heatA2Blocks_diagonal timeBonds side sidePositive stage rightTime))
  simpa only [completeOpenCubeHeatSpatialFourthActionPolynomial,
      openCubeHeatCayleyTraceSpatialFourthActionWickSum,
      noiseCount, leftBlocks, rightBlocks] using
    (finiteGaussianThirdCumulant_quartic_quadratic_wick
      noiseCount
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage leftTime)
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage rightTime)
      leftBlocks rightBlocks
      (completeOpenCubeHeatSpatialFourthActionQuarticRowBlocks
        timeBonds (bulkSourceWidth side) stage)
      (completeOpenCubeHeatSpatialFourthActionQuadraticRowSquares
        timeBonds (bulkSourceWidth side) stage)
      hleftBlocks hrightBlocks hleftSquares hrightSquares)

/-- Explicit connected value of the complete kinetic `V4`. -/
def openCubeHeatCayleyTraceKineticFourthActionWickSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  finiteGaussianWeightedRowBlocksWickSum noiseCount leftBlocks rightBlocks
      (completeOpenCubeHeatKineticFourthActionQuarticRowBlocks
        timeBonds (bulkSourceWidth side) stage) +
    finiteGaussianWeightedRowSquaresTriangleSum noiseCount
      (quadraticBlocksToSquares leftBlocks)
      (quadraticBlocksToSquares rightBlocks)
      (completeOpenCubeHeatKineticFourthActionQuadraticRowSquares
        timeBonds (bulkSourceWidth side) stage)

theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_kineticFourthAction_wick
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatKineticFourthActionPolynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceKineticFourthActionWickSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  have hleftBlocks := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage leftTime
  have hrightBlocks := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage rightTime
  have hleftSquares := hleftBlocks.trans
    (quadraticBlocksToSquares_polynomial noiseCount leftBlocks
      (heatA2Blocks_diagonal timeBonds side sidePositive stage leftTime))
  have hrightSquares := hrightBlocks.trans
    (quadraticBlocksToSquares_polynomial noiseCount rightBlocks
      (heatA2Blocks_diagonal timeBonds side sidePositive stage rightTime))
  simpa only [completeOpenCubeHeatKineticFourthActionPolynomial,
      openCubeHeatCayleyTraceKineticFourthActionWickSum,
      noiseCount, leftBlocks, rightBlocks] using
    (finiteGaussianThirdCumulant_quartic_quadratic_wick
      noiseCount
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage leftTime)
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage rightTime)
      leftBlocks rightBlocks
      (completeOpenCubeHeatKineticFourthActionQuarticRowBlocks
        timeBonds (bulkSourceWidth side) stage)
      (completeOpenCubeHeatKineticFourthActionQuadraticRowSquares
        timeBonds (bulkSourceWidth side) stage)
      hleftBlocks hrightBlocks hleftSquares hrightSquares)

/-- Explicit connected value of the complete Cayley-Haar `J2`. -/
def openCubeHeatCayleyTraceHaarJ2TriangleSum
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) : Q' :=
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  finiteGaussianWeightedRowSquaresTriangleSum noiseCount
    (quadraticBlocksToSquares leftBlocks)
    (quadraticBlocksToSquares rightBlocks)
    (completeOpenCubeHeatCayleyHaarJ2RowSquares
      timeBonds (bulkSourceWidth side) stage)

theorem finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_haarJ2_triangle
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds side)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage leftTime)
        (openCubeHeatBulkCayleyTraceA2
          timeBonds side sidePositive stage rightTime)
        (completeOpenCubeHeatCayleyHaarJ2Polynomial
          timeBonds (bulkSourceWidth side) stage) ≈
      openCubeHeatCayleyTraceHaarJ2TriangleSum
        timeBonds side sidePositive stage leftTime rightTime := by
  let noiseCount := bulkSourceNoiseCount timeBonds side
  let leftBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage leftTime
  let rightBlocks := openCubeHeatBulkCayleyTraceA2RowBlocks
    timeBonds side sidePositive stage rightTime
  let insertionSquares := completeOpenCubeHeatCayleyHaarJ2RowSquares
    timeBonds (bulkSourceWidth side) stage
  have hleftBlocks := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage leftTime
  have hrightBlocks := openCubeHeatBulkCayleyTraceA2_coeffEqv
    timeBonds side sidePositive stage rightTime
  have hleftSquares := hleftBlocks.trans
    (quadraticBlocksToSquares_polynomial noiseCount leftBlocks
      (heatA2Blocks_diagonal timeBonds side sidePositive stage leftTime))
  have hrightSquares := hrightBlocks.trans
    (quadraticBlocksToSquares_polynomial noiseCount rightBlocks
      (heatA2Blocks_diagonal timeBonds side sidePositive stage rightTime))
  simpa only [completeOpenCubeHeatCayleyHaarJ2Polynomial,
      openCubeHeatCayleyTraceHaarJ2TriangleSum,
      noiseCount, leftBlocks, rightBlocks, insertionSquares] using
    (finiteGaussianThirdCumulant_row_squares_triangle noiseCount
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage leftTime)
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage rightTime)
      (quadraticBlocksToSquares leftBlocks)
      (quadraticBlocksToSquares rightBlocks) insertionSquares
      hleftSquares hrightSquares)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatFourthActionHaarCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatFourthActionHaarCumulant.finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_spatialFourthAction_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatFourthActionHaarCumulant.finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_kineticFourthAction_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatFourthActionHaarCumulant.finiteGaussianThirdCumulant_openCubeHeat_cayleyTrace_haarJ2_triangle
