/-
# Exact open-cube Cayley trace-source coefficients

For the trace deficit `2 - chi₁` on one directed Cayley plaquette, the first
three nonzero chart coefficients are the exact local polynomials

  A₂ = H₂ = 4 * |B|²,
  A₃ = H₃,
  A₄ = F₄,

where `F₄` is the denominator-normalized Cayley quartic.  This leaf places
those three coefficients on the SAME finite rooted-comb/Heron rows and the
SAME rational bulk profile used by `bulkSourceHeronRadialSquare`.

The cubic action primitive already present in the library is `H₃/4`, so the
source cubic scales every one of its twenty-four signed row words by four.
The source quartic uses the normalized `F₄` row list directly; it is not the
heat-action coefficient `F₄/4 + F₂²/48 - F₂/6`.

The three coefficient certificates below are finite polynomial identities.
They do not assert convergence of a chart expansion, identify the ORIGINAL
interacting law with the Gaussian reference, supply OWN/OLD centers, control
a higher remainder, prove a uniform estimate, or establish a physical mass
gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant

/-- Exact scalar converting the spatial action cubic `H₃/4` to the trace
source cubic `H₃`. -/
def traceSourceCubicScale : Q' := 4

/-- Scale one weighted quadratic row block without changing its rows. -/
def scaleWeightedQuadraticRowBlock
    (scale : Q') (block : WeightedQuadraticRowBlock) :
    WeightedQuadraticRowBlock :=
  { weight := scale * block.weight
    first := block.first
    second := block.second }

/-- Scale one weighted cubic row block without changing its rows. -/
def scaleWeightedCubicRowBlock
    (scale : Q') (block : WeightedCubicRowBlock) : WeightedCubicRowBlock :=
  { weight := scale * block.weight
    first := block.first
    second := block.second
    third := block.third }

/-- Scale one weighted quartic row block without changing its rows. -/
def scaleWeightedQuarticRowBlock
    (scale : Q') (block : WeightedQuarticRowBlock) :
    WeightedQuarticRowBlock :=
  { weight := scale * block.weight
    first := block.first
    second := block.second
    third := block.third
    fourth := block.fourth }

private theorem polySum_congr {Index : Type}
    (left right : Index → RatPoly) : ∀ items : List Index,
    (∀ item, item ∈ items → RatPolyCoeffEqv (left item) (right item)) →
    RatPolyCoeffEqv (polySum (items.map left)) (polySum (items.map right))
  | [], _ => RatPolyCoeffEqv.refl _
  | item :: items, hypothesis =>
      RatPolyCoeffEqv.add
        (hypothesis item List.mem_cons_self)
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
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.smul_add scale polynomial (polySum polynomials))
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
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
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (weightedTermPolynomial_flatMap block items))
        (weightedTermPolynomial_append (block item) (items.flatMap block))

private theorem weightedQuadraticBlocks_scale
    (coordinateCount : Nat) (scale : Q') :
    ∀ blocks : List WeightedQuadraticRowBlock,
    RatPolyCoeffEqv
      (polySmul scale
        (weightedTermPolynomial
          (blocks.map (weightedQuadraticRowBlockTerm coordinateCount))))
      (weightedTermPolynomial
        ((blocks.map (scaleWeightedQuadraticRowBlock scale)).map
          (weightedQuadraticRowBlockTerm coordinateCount))) := by
  intro blocks
  unfold weightedTermPolynomial weightedQuadraticRowBlockTerm
    scaleWeightedQuadraticRowBlock
  simp only [List.map_map]
  change RatPolyCoeffEqv
    (polySmul scale
      (polySum (blocks.map fun block =>
        polySmul block.weight
          (finiteGaussianRowWord coordinateCount
            [block.first, block.second]))))
    (polySum (blocks.map fun block =>
      polySmul (scale * block.weight)
        (finiteGaussianRowWord coordinateCount
          [block.first, block.second])))
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
  exact RatPolyCoeffEqv.trans distribute
    (polySum_congr _ _ blocks (fun block _ =>
      RatPolyCoeffEqv.smul_assoc scale block.weight _))

private theorem weightedCubicBlocks_scale
    (coordinateCount : Nat) (scale : Q') :
    ∀ blocks : List WeightedCubicRowBlock,
    RatPolyCoeffEqv
      (polySmul scale
        (weightedTermPolynomial
          (blocks.map (weightedCubicRowBlockTerm coordinateCount))))
      (weightedTermPolynomial
        ((blocks.map (scaleWeightedCubicRowBlock scale)).map
          (weightedCubicRowBlockTerm coordinateCount))) := by
  intro blocks
  unfold weightedTermPolynomial weightedCubicRowBlockTerm
    scaleWeightedCubicRowBlock
  simp only [List.map_map]
  change RatPolyCoeffEqv
    (polySmul scale
      (polySum (blocks.map fun block =>
        polySmul block.weight
          (finiteGaussianRowWord coordinateCount
            [block.first, block.second, block.third]))))
    (polySum (blocks.map fun block =>
      polySmul (scale * block.weight)
        (finiteGaussianRowWord coordinateCount
          [block.first, block.second, block.third])))
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
  exact RatPolyCoeffEqv.trans distribute
    (polySum_congr _ _ blocks (fun block _ =>
      RatPolyCoeffEqv.smul_assoc scale block.weight _))

private theorem weightedQuarticBlocks_scale
    (coordinateCount : Nat) (scale : Q') :
    ∀ blocks : List WeightedQuarticRowBlock,
    RatPolyCoeffEqv
      (polySmul scale
        (weightedTermPolynomial
          (blocks.map (weightedQuarticRowBlockTerm coordinateCount))))
      (weightedTermPolynomial
        ((blocks.map (scaleWeightedQuarticRowBlock scale)).map
          (weightedQuarticRowBlockTerm coordinateCount))) := by
  intro blocks
  unfold weightedTermPolynomial weightedQuarticRowBlockTerm
    scaleWeightedQuarticRowBlock
  simp only [List.map_map]
  change RatPolyCoeffEqv
    (polySmul scale
      (polySum (blocks.map fun block =>
        polySmul block.weight
          (finiteGaussianRowWord coordinateCount
            [block.first, block.second, block.third, block.fourth]))))
    (polySum (blocks.map fun block =>
      polySmul (scale * block.weight)
        (finiteGaussianRowWord coordinateCount
          [block.first, block.second, block.third, block.fourth])))
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
  exact RatPolyCoeffEqv.trans distribute
    (polySum_congr _ _ blocks (fun block _ =>
      RatPolyCoeffEqv.smul_assoc scale block.weight _))

/-- Actual trace-source quadratic coefficient `H₂=4|B|²` at one history
time, with the existing bulk profile outside each color-row square. -/
def openCubeBulkCayleyTraceA2
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : RatPoly :=
  polySmul 4
    (bulkSourceHeronRadialSquare
      timeBonds side sidePositive stage time)

/-- Explicit weighted two-row blocks of the trace-source quadratic. -/
def openCubeBulkCayleyTraceA2RowBlocks
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : List WeightedQuadraticRowBlock :=
  (bulkSourceHeronQuadraticRowBlocks
    timeBonds side sidePositive stage time).map
      (scaleWeightedQuadraticRowBlock 4)

/-- The literal trace-source `A₂` is exactly its displayed weighted two-row
list. -/
theorem openCubeBulkCayleyTraceA2_coeffEqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    RatPolyCoeffEqv
      (openCubeBulkCayleyTraceA2
        timeBonds side sidePositive stage time)
      (weightedTermPolynomial
        ((openCubeBulkCayleyTraceA2RowBlocks
          timeBonds side sidePositive stage time).map
            (weightedQuadraticRowBlockTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  unfold openCubeBulkCayleyTraceA2 openCubeBulkCayleyTraceA2RowBlocks
  let coordinateCount := bulkSourceNoiseCount timeBonds side
  let blocks := bulkSourceHeronQuadraticRowBlocks
    timeBonds side sidePositive stage time
  rw [bulkSourceHeronRadialSquare_eq_quadraticTerms,
    bulkSourceHeronQuadraticTerms_eq_rowBlocks]
  change RatPolyCoeffEqv
    (polySmul 4
      (weightedTermPolynomial
        (blocks.map (weightedQuadraticRowBlockTerm coordinateCount))))
    (weightedTermPolynomial
      ((blocks.map (scaleWeightedQuadraticRowBlock 4)).map
        (weightedQuadraticRowBlockTerm coordinateCount)))
  exact weightedQuadraticBlocks_scale coordinateCount 4 blocks

/-- Actual trace-source cubic coefficient `H₃`, summed over the weighted bulk
faces at one history time.  The local action polynomial is `H₃/4`, hence the
factor `4 * profileWeight`. -/
def openCubeBulkCayleyTraceA3
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : RatPoly :=
  polySum ((bulkSourceFaces side).map fun face =>
    polySmul
      (traceSourceCubicScale * bulkSourceCoefficient side sidePositive face)
      (combGaugeFreeHistoryPlaquetteSpatialCubicPolynomial
        timeBonds (bulkSourceWidth side) stage time face))

/-- Explicit weighted three-row blocks of the complete trace-source cubic. -/
def openCubeBulkCayleyTraceA3RowBlocks
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : List WeightedCubicRowBlock :=
  (bulkSourceFaces side).flatMap fun face =>
    (openCubePlaquetteSpatialCubicRowBlocks
      timeBonds (bulkSourceWidth side) stage time face).map
        (scaleWeightedCubicRowBlock
          (traceSourceCubicScale *
            bulkSourceCoefficient side sidePositive face))

/-- The literal trace-source `A₃` is exactly its flattened weighted list of
`H₃` three-row words. -/
theorem openCubeBulkCayleyTraceA3_coeffEqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    RatPolyCoeffEqv
      (openCubeBulkCayleyTraceA3
        timeBonds side sidePositive stage time)
      (weightedTermPolynomial
        ((openCubeBulkCayleyTraceA3RowBlocks
          timeBonds side sidePositive stage time).map
            (weightedCubicRowBlockTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  let coordinateCount := bulkSourceNoiseCount timeBonds side
  let faces := bulkSourceFaces side
  let baseBlocks := fun face : Z4Plaq =>
    openCubePlaquetteSpatialCubicRowBlocks
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
          (combGaugeFreeHistoryPlaquetteSpatialCubicPolynomial
            timeBonds (bulkSourceWidth side) stage time face))
        (weightedTermPolynomial (sourceTerms face)) := by
    intro face _
    have scaleCertificate := weightedCubicBlocks_scale coordinateCount
      (sourceScale face) (baseBlocks face)
    have baseCertificate : RatPolyCoeffEqv
        (combGaugeFreeHistoryPlaquetteSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage time face)
        (weightedTermPolynomial
          ((baseBlocks face).map
            (weightedCubicRowBlockTerm coordinateCount))) := by
      unfold combGaugeFreeHistoryPlaquetteSpatialCubicPolynomial
        finiteGaussianCayleySpatialCubicPolynomial baseBlocks
        openCubePlaquetteSpatialCubicRowBlocks
      rw [noiseEquality]
      exact RatPolyCoeffEqv.refl _
    exact RatPolyCoeffEqv.trans
      (baseCertificate.smul (sourceScale face))
      (by simpa only [sourceTerms] using scaleCertificate)
  have sumCertificate := polySum_congr _ _ faces faceCertificates
  have flatCertificate := weightedTermPolynomial_flatMap sourceTerms faces
  unfold openCubeBulkCayleyTraceA3
    openCubeBulkCayleyTraceA3RowBlocks
  change RatPolyCoeffEqv
    (polySum (faces.map fun face =>
      polySmul (sourceScale face)
        (combGaugeFreeHistoryPlaquetteSpatialCubicPolynomial
          timeBonds (bulkSourceWidth side) stage time face)))
    (weightedTermPolynomial
      ((faces.flatMap fun face =>
        (baseBlocks face).map
          (scaleWeightedCubicRowBlock (sourceScale face))).map
            (weightedCubicRowBlockTerm coordinateCount)))
  exact RatPolyCoeffEqv.trans sumCertificate
    (by simpa only [List.map_flatMap] using flatCertificate)

/-- Actual trace-source normalized Cayley quartic `F₄`, summed over the same
weighted bulk faces at one history time. -/
def openCubeBulkCayleyTraceA4
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : RatPoly :=
  polySum ((bulkSourceFaces side).map fun face =>
    polySmul (bulkSourceCoefficient side sidePositive face)
      (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
        timeBonds (bulkSourceWidth side) stage time face))

/-- Explicit weighted four-row blocks of the complete trace-source quartic. -/
def openCubeBulkCayleyTraceA4RowBlocks
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) : List WeightedQuarticRowBlock :=
  (bulkSourceFaces side).flatMap fun face =>
    (openCubePlaquetteNormalizedH4RowBlocks
      timeBonds (bulkSourceWidth side) stage time face).map
        (scaleWeightedQuarticRowBlock
          (bulkSourceCoefficient side sidePositive face))

/-- The literal trace-source `A₄` is exactly its flattened weighted list of
normalized-Cayley four-row words. -/
theorem openCubeBulkCayleyTraceA4_coeffEqv
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage time : Nat) :
    RatPolyCoeffEqv
      (openCubeBulkCayleyTraceA4
        timeBonds side sidePositive stage time)
      (weightedTermPolynomial
        ((openCubeBulkCayleyTraceA4RowBlocks
          timeBonds side sidePositive stage time).map
            (weightedQuarticRowBlockTerm
              (bulkSourceNoiseCount timeBonds side)))) := by
  let coordinateCount := bulkSourceNoiseCount timeBonds side
  let faces := bulkSourceFaces side
  let baseBlocks := fun face : Z4Plaq =>
    openCubePlaquetteNormalizedH4RowBlocks
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
          (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
            timeBonds (bulkSourceWidth side) stage time face))
        (weightedTermPolynomial (sourceTerms face)) := by
    intro face _
    let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
      timeBonds (bulkSourceWidth side) stage time face
    have quarticCertificate :=
      finiteGaussianNormalizedCayleyH4Polynomial_quarticTerms
        coordinateCount (rows 0) (rows 1) (rows 2) (rows 3)
    rw [finiteGaussianNormalizedCayleyH4QuarticTerms_eq_rowBlocks]
      at quarticCertificate
    have actualCertificate : RatPolyCoeffEqv
        (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
          timeBonds (bulkSourceWidth side) stage time face)
        (weightedTermPolynomial
          ((openCubePlaquetteNormalizedH4RowBlocks
            timeBonds (bulkSourceWidth side) stage time face).map
            (weightedQuarticRowBlockTerm coordinateCount))) := by
      unfold combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
      rw [noiseEquality]
      exact quarticCertificate
    have scaleCertificate := weightedQuarticBlocks_scale coordinateCount
      (sourceScale face) (baseBlocks face)
    exact RatPolyCoeffEqv.trans
      (actualCertificate.smul (sourceScale face))
      (by simpa only [baseBlocks, sourceTerms] using scaleCertificate)
  have sumCertificate := polySum_congr _ _ faces faceCertificates
  have flatCertificate := weightedTermPolynomial_flatMap sourceTerms faces
  unfold openCubeBulkCayleyTraceA4
    openCubeBulkCayleyTraceA4RowBlocks
  change RatPolyCoeffEqv
    (polySum (faces.map fun face =>
      polySmul (sourceScale face)
        (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
          timeBonds (bulkSourceWidth side) stage time face)))
    (weightedTermPolynomial
      ((faces.flatMap fun face =>
        (baseBlocks face).map
          (scaleWeightedQuarticRowBlock (sourceScale face))).map
            (weightedQuarticRowBlockTerm coordinateCount)))
  exact RatPolyCoeffEqv.trans sumCertificate
    (by simpa only [List.map_flatMap] using flatCertificate)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients.openCubeBulkCayleyTraceA2_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients.openCubeBulkCayleyTraceA3_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients.openCubeBulkCayleyTraceA4_coeffEqv
