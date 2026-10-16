/-
# Heat-normalized open-cube Cayley trace-source coefficients

This leaf places the exact trace-deficit coefficients

  A2 = H2 = 4|B|^2,
  A3 = H3,
  A4 = F4

on the heat-normalized directed plaquette rows whose Heron transform targets
the exact inverse of `2L`.  Each literal polynomial is identified with its
finite weighted row-block list, so the existing Wick compilers can consume
the corrected carrier without any new Gaussian moment premise.

The file does not assemble the complete action/density coefficients, OWN/OLD
response, a uniform sign, ORIGINAL-law comparison, continuum theory, or
physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows

local infix:50 " ≈ " => Q'.eqv

private theorem polySum_congr {Index : Type}
    (left right : Index → RatPoly) : ∀ items : List Index,
    (∀ item, item ∈ items → RatPolyCoeffEqv (left item) (right item)) →
    RatPolyCoeffEqv (polySum (items.map left)) (polySum (items.map right))
  | [], _ => RatPolyCoeffEqv.refl _
  | item :: items, hypothesis =>
      (hypothesis item List.mem_cons_self).add
        (polySum_congr left right items
          (fun other membership =>
            hypothesis other (List.mem_cons_of_mem item membership)))

private theorem polySmul_polySum (scale : Q') : ∀ polynomials : List RatPoly,
    RatPolyCoeffEqv
      (polySmul scale (polySum polynomials))
      (polySum (polynomials.map fun polynomial =>
        polySmul scale polynomial))
  | [] => RatPolyCoeffEqv.zero_smul polyZero
  | polynomial :: polynomials =>
      (RatPolyCoeffEqv.smul_add scale polynomial (polySum polynomials)).trans
        ((RatPolyCoeffEqv.refl _).add
          (polySmul_polySum scale polynomials))

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

private theorem weightedQuadraticBlocks_scale
    (coordinateCount : Nat) (scale : Q')
    (blocks : List WeightedQuadraticRowBlock) :
    RatPolyCoeffEqv
      (polySmul scale
        (weightedTermPolynomial
          (blocks.map (weightedQuadraticRowBlockTerm coordinateCount))))
      (weightedTermPolynomial
        ((blocks.map (scaleWeightedQuadraticRowBlock scale)).map
          (weightedQuadraticRowBlockTerm coordinateCount))) := by
  unfold weightedTermPolynomial weightedQuadraticRowBlockTerm
    scaleWeightedQuadraticRowBlock
  simp only [List.map_map]
  have distribute : RatPolyCoeffEqv
      (polySmul scale
        (polySum (blocks.map fun block =>
          polySmul block.weight
            (finiteGaussianRowWord coordinateCount
              [block.first, block.second]))))
      (polySum (blocks.map fun block =>
        polySmul scale
          (polySmul block.weight
            (finiteGaussianRowWord coordinateCount
              [block.first, block.second])))) := by
    simpa only [List.map_map, Function.comp_apply] using
      polySmul_polySum scale
        (blocks.map fun block =>
          polySmul block.weight
            (finiteGaussianRowWord coordinateCount
              [block.first, block.second]))
  exact distribute.trans
    (polySum_congr _ _ blocks (fun block _ =>
      RatPolyCoeffEqv.smul_assoc scale block.weight _))

private theorem weightedCubicBlocks_scale
    (coordinateCount : Nat) (scale : Q')
    (blocks : List WeightedCubicRowBlock) :
    RatPolyCoeffEqv
      (polySmul scale
        (weightedTermPolynomial
          (blocks.map (weightedCubicRowBlockTerm coordinateCount))))
      (weightedTermPolynomial
        ((blocks.map (scaleWeightedCubicRowBlock scale)).map
          (weightedCubicRowBlockTerm coordinateCount))) := by
  unfold weightedTermPolynomial weightedCubicRowBlockTerm
    scaleWeightedCubicRowBlock
  simp only [List.map_map]
  have distribute : RatPolyCoeffEqv
      (polySmul scale
        (polySum (blocks.map fun block =>
          polySmul block.weight
            (finiteGaussianRowWord coordinateCount
              [block.first, block.second, block.third]))))
      (polySum (blocks.map fun block =>
        polySmul scale
          (polySmul block.weight
            (finiteGaussianRowWord coordinateCount
              [block.first, block.second, block.third])))) := by
    simpa only [List.map_map, Function.comp_apply] using
      polySmul_polySum scale
        (blocks.map fun block =>
          polySmul block.weight
            (finiteGaussianRowWord coordinateCount
              [block.first, block.second, block.third]))
  exact distribute.trans
    (polySum_congr _ _ blocks (fun block _ =>
      RatPolyCoeffEqv.smul_assoc scale block.weight _))

private theorem weightedQuarticBlocks_scale
    (coordinateCount : Nat) (scale : Q')
    (blocks : List WeightedQuarticRowBlock) :
    RatPolyCoeffEqv
      (polySmul scale
        (weightedTermPolynomial
          (blocks.map (weightedQuarticRowBlockTerm coordinateCount))))
      (weightedTermPolynomial
        ((blocks.map (scaleWeightedQuarticRowBlock scale)).map
          (weightedQuarticRowBlockTerm coordinateCount))) := by
  unfold weightedTermPolynomial weightedQuarticRowBlockTerm
    scaleWeightedQuarticRowBlock
  simp only [List.map_map]
  have distribute : RatPolyCoeffEqv
      (polySmul scale
        (polySum (blocks.map fun block =>
          polySmul block.weight
            (finiteGaussianRowWord coordinateCount
              [block.first, block.second, block.third, block.fourth]))))
      (polySum (blocks.map fun block =>
        polySmul scale
          (polySmul block.weight
            (finiteGaussianRowWord coordinateCount
              [block.first, block.second, block.third, block.fourth])))) := by
    simpa only [List.map_map, Function.comp_apply] using
      polySmul_polySum scale
        (blocks.map fun block =>
          polySmul block.weight
            (finiteGaussianRowWord coordinateCount
              [block.first, block.second, block.third, block.fourth]))
  exact distribute.trans
    (polySum_congr _ _ blocks (fun block _ =>
      RatPolyCoeffEqv.smul_assoc scale block.weight _))

/-- Heat-normalized weighted quadratic row blocks of one bulk source. -/
def bulkSourceHeatQuadraticRowBlocks
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : List WeightedQuadraticRowBlock :=
  (List.range (3 * (bulkSourceFaces side).length)).map fun rowIndex =>
    let row := bulkSourceHeatHeronColorCurlRow
      timeBonds side stage time rowIndex
    { weight := bulkSourceIndexWeight side sidePositive (rowIndex / 3)
      first := row
      second := row }

/-- Weighted two-row blocks of heat-normalized `A2`. -/
def openCubeHeatBulkCayleyTraceA2RowBlocks
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : List WeightedQuadraticRowBlock :=
  (bulkSourceHeatQuadraticRowBlocks
    timeBonds side sidePositive stage time).map
      (scaleWeightedQuadraticRowBlock 4)

theorem openCubeHeatBulkCayleyTraceA2_coeffEqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    RatPolyCoeffEqv
      (openCubeHeatBulkCayleyTraceA2
        timeBonds side sidePositive stage time)
      (weightedTermPolynomial
        ((openCubeHeatBulkCayleyTraceA2RowBlocks
          timeBonds side sidePositive stage time).map
            (weightedQuadraticRowBlockTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  let coordinateCount := bulkSourceNoiseCount timeBonds side
  let blocks := bulkSourceHeatQuadraticRowBlocks
    timeBonds side sidePositive stage time
  have hbase : RatPolyCoeffEqv
      (bulkSourceHeatHeronRadialSquare
        timeBonds side sidePositive stage time)
      (weightedTermPolynomial
        (blocks.map (weightedQuadraticRowBlockTerm coordinateCount))) := by
    simp only [blocks]
    unfold bulkSourceHeatHeronRadialSquare
      combGaugeHeatFreeHistoryHeronWeightedCurlRadialSquare
      bulkSourceHeatQuadraticRowBlocks weightedTermPolynomial
      weightedQuadraticRowBlockTerm finiteGaussianWeightedRadialSquare
      finiteGaussianRowSquare finiteGaussianRowWord coordinateCount
      bulkSourceNoiseCount
    simp only [List.map_map]
    exact RatPolyCoeffEqv.refl _
  unfold openCubeHeatBulkCayleyTraceA2
    openCubeHeatBulkCayleyTraceA2RowBlocks
  exact (hbase.smul 4).trans
    (weightedQuadraticBlocks_scale coordinateCount 4 blocks)

/-- Heat-normalized `H3/4` row blocks on one directed plaquette. -/
def openCubeHeatPlaquetteSpatialCubicRowBlocks
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedCubicRowBlock :=
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianCayleySpatialCubicRowBlocks
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Literal heat-normalized `H3/4` polynomial on one plaquette. -/
def openCubeHeatPlaquetteSpatialCubicPolynomial
    (timeBonds width stage time : Nat) (face : Z4Plaq) : RatPoly :=
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianCayleySpatialCubicPolynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Heat-normalized trace-source cubic `A3=H3`. -/
def openCubeHeatBulkCayleyTraceA3
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : RatPoly :=
  polySum ((bulkSourceFaces side).map fun face =>
    polySmul
      (traceSourceCubicScale * bulkSourceCoefficient side sidePositive face)
      (openCubeHeatPlaquetteSpatialCubicPolynomial
        timeBonds (bulkSourceWidth side) stage time face))

/-- Weighted row blocks of heat-normalized `A3`. -/
def openCubeHeatBulkCayleyTraceA3RowBlocks
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : List WeightedCubicRowBlock :=
  (bulkSourceFaces side).flatMap fun face =>
    (openCubeHeatPlaquetteSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage time face).map
        (scaleWeightedCubicRowBlock
          (traceSourceCubicScale *
            bulkSourceCoefficient side sidePositive face))

theorem openCubeHeatBulkCayleyTraceA3_coeffEqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    RatPolyCoeffEqv
      (openCubeHeatBulkCayleyTraceA3
        timeBonds side sidePositive stage time)
      (weightedTermPolynomial
        ((openCubeHeatBulkCayleyTraceA3RowBlocks
          timeBonds side sidePositive stage time).map
            (weightedCubicRowBlockTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  let coordinateCount := bulkSourceNoiseCount timeBonds side
  let faces := bulkSourceFaces side
  let baseBlocks := fun face : Z4Plaq =>
    openCubeHeatPlaquetteSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage time face
  let sourceScale := fun face : Z4Plaq =>
    traceSourceCubicScale * bulkSourceCoefficient side sidePositive face
  let sourceTerms := fun face : Z4Plaq =>
    ((baseBlocks face).map
      (scaleWeightedCubicRowBlock (sourceScale face))).map
        (weightedCubicRowBlockTerm coordinateCount)
  have noiseEquality : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) = coordinateCount := by
    unfold combGaugePlaquetteNoiseCount coordinateCount bulkSourceNoiseCount
    rfl
  have faceCertificates : ∀ face, face ∈ faces →
      RatPolyCoeffEqv
        (polySmul (sourceScale face)
          (openCubeHeatPlaquetteSpatialCubicPolynomial
            timeBonds (bulkSourceWidth side) stage time face))
        (weightedTermPolynomial (sourceTerms face)) := by
    intro face _
    have hbase : RatPolyCoeffEqv
        (openCubeHeatPlaquetteSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage time face)
        (weightedTermPolynomial
          ((baseBlocks face).map
            (weightedCubicRowBlockTerm coordinateCount))) := by
      unfold openCubeHeatPlaquetteSpatialCubicPolynomial baseBlocks
        openCubeHeatPlaquetteSpatialCubicRowBlocks
        finiteGaussianCayleySpatialCubicPolynomial
      rw [noiseEquality]
      exact RatPolyCoeffEqv.refl _
    have hscale := weightedCubicBlocks_scale coordinateCount
      (sourceScale face) (baseBlocks face)
    exact (hbase.smul (sourceScale face)).trans
      (by simpa only [sourceTerms] using hscale)
  have hsum := polySum_congr _ _ faces faceCertificates
  have hflat := weightedTermPolynomial_flatMap sourceTerms faces
  unfold openCubeHeatBulkCayleyTraceA3
    openCubeHeatBulkCayleyTraceA3RowBlocks
  change RatPolyCoeffEqv
    (polySum (faces.map fun face =>
      polySmul (sourceScale face)
        (openCubeHeatPlaquetteSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage time face)))
    (weightedTermPolynomial
      ((faces.flatMap fun face =>
        (baseBlocks face).map
          (scaleWeightedCubicRowBlock (sourceScale face))).map
            (weightedCubicRowBlockTerm coordinateCount)))
  exact hsum.trans (by
    simpa only [List.map_flatMap] using hflat)

/-- Heat-normalized normalized-Cayley quartic on one plaquette. -/
def openCubeHeatPlaquetteNormalizedH4Polynomial
    (timeBonds width stage time : Nat) (face : Z4Plaq) : RatPoly :=
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianNormalizedCayleyH4Polynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Heat-normalized normalized-Cayley quartic row blocks. -/
def openCubeHeatPlaquetteNormalizedH4RowBlocks
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedQuarticRowBlock :=
  let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianNormalizedCayleyH4QuarticRowBlocks
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Heat-normalized trace-source quartic `A4=F4`. -/
def openCubeHeatBulkCayleyTraceA4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : RatPoly :=
  polySum ((bulkSourceFaces side).map fun face =>
    polySmul (bulkSourceCoefficient side sidePositive face)
      (openCubeHeatPlaquetteNormalizedH4Polynomial
        timeBonds (bulkSourceWidth side) stage time face))

/-- Weighted row blocks of heat-normalized `A4`. -/
def openCubeHeatBulkCayleyTraceA4RowBlocks
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : List WeightedQuarticRowBlock :=
  (bulkSourceFaces side).flatMap fun face =>
    (openCubeHeatPlaquetteNormalizedH4RowBlocks
      timeBonds (bulkSourceWidth side) stage time face).map
        (scaleWeightedQuarticRowBlock
          (bulkSourceCoefficient side sidePositive face))

theorem openCubeHeatBulkCayleyTraceA4_coeffEqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    RatPolyCoeffEqv
      (openCubeHeatBulkCayleyTraceA4
        timeBonds side sidePositive stage time)
      (weightedTermPolynomial
        ((openCubeHeatBulkCayleyTraceA4RowBlocks
          timeBonds side sidePositive stage time).map
            (weightedQuarticRowBlockTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  let coordinateCount := bulkSourceNoiseCount timeBonds side
  let faces := bulkSourceFaces side
  let baseBlocks := fun face : Z4Plaq =>
    openCubeHeatPlaquetteNormalizedH4RowBlocks
      timeBonds (bulkSourceWidth side) stage time face
  let sourceScale := fun face : Z4Plaq =>
    bulkSourceCoefficient side sidePositive face
  let sourceTerms := fun face : Z4Plaq =>
    ((baseBlocks face).map
      (scaleWeightedQuarticRowBlock (sourceScale face))).map
        (weightedQuarticRowBlockTerm coordinateCount)
  have noiseEquality : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth side) = coordinateCount := by
    unfold combGaugePlaquetteNoiseCount coordinateCount bulkSourceNoiseCount
    rfl
  have faceCertificates : ∀ face, face ∈ faces →
      RatPolyCoeffEqv
        (polySmul (sourceScale face)
          (openCubeHeatPlaquetteNormalizedH4Polynomial
            timeBonds (bulkSourceWidth side) stage time face))
        (weightedTermPolynomial (sourceTerms face)) := by
    intro face _
    let rows := combGaugeHeatFreeHistoryHeronDirectedPlaquetteRows
      timeBonds (bulkSourceWidth side) stage time face
    have hquartic :=
      finiteGaussianNormalizedCayleyH4Polynomial_quarticTerms
        coordinateCount (rows 0) (rows 1) (rows 2) (rows 3)
    rw [finiteGaussianNormalizedCayleyH4QuarticTerms_eq_rowBlocks]
      at hquartic
    have hbase : RatPolyCoeffEqv
        (openCubeHeatPlaquetteNormalizedH4Polynomial
          timeBonds (bulkSourceWidth side) stage time face)
        (weightedTermPolynomial
          ((baseBlocks face).map
            (weightedQuarticRowBlockTerm coordinateCount))) := by
      unfold openCubeHeatPlaquetteNormalizedH4Polynomial baseBlocks
        openCubeHeatPlaquetteNormalizedH4RowBlocks
      rw [noiseEquality]
      exact hquartic
    have hscale := weightedQuarticBlocks_scale coordinateCount
      (sourceScale face) (baseBlocks face)
    exact (hbase.smul (sourceScale face)).trans
      (by simpa only [sourceTerms] using hscale)
  have hsum := polySum_congr _ _ faces faceCertificates
  have hflat := weightedTermPolynomial_flatMap sourceTerms faces
  unfold openCubeHeatBulkCayleyTraceA4
    openCubeHeatBulkCayleyTraceA4RowBlocks
  change RatPolyCoeffEqv
    (polySum (faces.map fun face =>
      polySmul (sourceScale face)
        (openCubeHeatPlaquetteNormalizedH4Polynomial
          timeBonds (bulkSourceWidth side) stage time face)))
    (weightedTermPolynomial
      ((faces.flatMap fun face =>
        (baseBlocks face).map
          (scaleWeightedQuarticRowBlock (sourceScale face))).map
            (weightedQuarticRowBlockTerm coordinateCount)))
  exact hsum.trans (by
    simpa only [List.map_flatMap] using hflat)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients.openCubeHeatBulkCayleyTraceA2_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients.openCubeHeatBulkCayleyTraceA3_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCayleySourceCoefficients.openCubeHeatBulkCayleyTraceA4_coeffEqv
