/-
# Actual open-cube bulk-source/Cayley-Haar quadratic cumulant

The product Cayley-chart Haar density contributes the quadratic coefficient

  J2 = -3 * sum_(history slices, gauge-fixed links) |a|^2.

This leaf constructs that finite FREE reference insertion on the SAME
rooted-comb/Heron history carrier used by the spatial and kinetic leaves.  Its
canonical family includes every one of the `timeBonds+1` history slices and
every comb-gauge edge.  The insertion against two literal bulk-source
quadratics reduces term-by-term to the checked three-square Gram triangle.

This is the reference product-chart Haar term.  It is not an identification
of the ORIGINAL gauge-reduced Jacobian or regauging density, and it does not
include the cubic-pair, action, source-renormalization or higher-remainder
terms of the full order-six response.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Three weighted row squares of one Cayley-chart Haar coefficient
`-3*|a|^2`. -/
def finiteGaussianCayleyHaarJ2RowSquares
    (rows : Nat → Nat → Q') : List WeightedRowSquare :=
  finiteGaussianWeightedRowNormSquares (-3) rows

/-- Literal `-3*|a|^2` polynomial for one three-color row triple. -/
def finiteGaussianCayleyHaarJ2Polynomial
    (N : Nat) (rows : Nat → Nat → Q') : RatPoly :=
  weightedTermPolynomial
    ((finiteGaussianCayleyHaarJ2RowSquares rows).map
      (weightedRowSquareTerm N))

/-- The three row-square blocks are coefficientwise exactly the local Cayley
Haar density coefficient `-3*|a|^2`. -/
theorem finiteGaussianCayleyHaarJ2Polynomial_coeffEqv
    (N : Nat) (rows : Nat → Nat → Q') :
    RatPolyCoeffEqv
      (polySmul (-3) (finiteGaussianRowDot N 3 rows rows))
      (finiteGaussianCayleyHaarJ2Polynomial N rows) :=
  finiteGaussianWeightedRowNormSquares_coeffEqv N (-3) rows

/-- Actual local Cayley-Haar `J2` row squares on one comb-gauge edge and one
history slice. -/
def openCubeCayleyHaarJ2RowSquares
    (timeBonds width stage time : Nat) (link : Z4Link) :
    List WeightedRowSquare :=
  finiteGaussianCayleyHaarJ2RowSquares
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage time link)

/-- Actual local Cayley-Haar `J2` polynomial on one comb-gauge edge and one
history slice. -/
def combGaugeFreeHistoryCayleyHaarJ2Polynomial
    (timeBonds width stage time : Nat) (link : Z4Link) : RatPoly :=
  finiteGaussianCayleyHaarJ2Polynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage time link)

/-- Exact Gram-triangle value for one local Cayley-Haar insertion against two
actual bulk-source times. -/
def openCubeBulkCayleyHaarJ2TriangleSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (link : Z4Link) : Q' :=
  finiteGaussianWeightedRowSquaresTriangleSum
    (bulkSourceNoiseCount timeBonds s)
    (bulkSourceHeronWeightedRowSquares timeBonds s hs stage leftTime)
    (bulkSourceHeronWeightedRowSquares timeBonds s hs stage rightTime)
    (openCubeCayleyHaarJ2RowSquares
      timeBonds (bulkSourceWidth s) stage insertionTime link)

/-- One actual local Cayley-Haar `J2` insertion reduces to the displayed
finite weighted sum of Gram triangles. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_cayleyHaarJ2_triangle
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (link : Z4Link) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
        (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
        (combGaugeFreeHistoryCayleyHaarJ2Polynomial
          timeBonds (bulkSourceWidth s) stage insertionTime link) ≈
      openCubeBulkCayleyHaarJ2TriangleSum
        timeBonds s hs stage leftTime rightTime insertionTime link := by
  let N := bulkSourceNoiseCount timeBonds s
  let leftSquares := bulkSourceHeronWeightedRowSquares
    timeBonds s hs stage leftTime
  let rightSquares := bulkSourceHeronWeightedRowSquares
    timeBonds s hs stage rightTime
  let insertionSquares := openCubeCayleyHaarJ2RowSquares
    timeBonds (bulkSourceWidth s) stage insertionTime link
  rw [bulkSourceHeronRadialSquare_eq_weightedRowSquares,
    bulkSourceHeronRadialSquare_eq_weightedRowSquares]
  change finiteGaussianThirdCumulant N
      (weightedTermPolynomial
        (leftSquares.map (weightedRowSquareTerm N)))
      (weightedTermPolynomial
        (rightSquares.map (weightedRowSquareTerm N)))
      (weightedTermPolynomial
        (insertionSquares.map (weightedRowSquareTerm N))) ≈
    finiteGaussianWeightedRowSquaresTriangleSum
      N leftSquares rightSquares insertionSquares
  exact finiteGaussianThirdCumulant_weighted_row_squares_triangle
    N leftSquares rightSquares insertionSquares

/-- Arbitrary scalar OLD centers cancel inside the connected local Cayley-Haar
insertion. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_cayleyHaarJ2_triangle
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (link : Z4Link)
    (leftOldCenter rightOldCenter : Q') :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
        (combGaugeFreeHistoryCayleyHaarJ2Polynomial
          timeBonds (bulkSourceWidth s) stage insertionTime link) ≈
      openCubeBulkCayleyHaarJ2TriangleSum
        timeBonds s hs stage leftTime rightTime insertionTime link :=
  Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_center_left_middle
      (bulkSourceNoiseCount timeBonds s) leftOldCenter rightOldCenter
      (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
      (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
      (combGaugeFreeHistoryCayleyHaarJ2Polynomial
        timeBonds (bulkSourceWidth s) stage insertionTime link))
    (finiteGaussianThirdCumulant_openCube_bulk_cayleyHaarJ2_triangle
      timeBonds s hs stage leftTime rightTime insertionTime link)

/-- One weighted local Cayley-Haar insertion. -/
structure OpenCubeCayleyHaarJ2Insertion where
  weight : Q'
  time : Nat
  link : Z4Link

/-- Canonical reference Cayley-Haar list: every history slice and every
comb-gauge edge. -/
def completeOpenCubeCayleyHaarJ2Insertions
    (timeBonds width : Nat) : List OpenCubeCayleyHaarJ2Insertion :=
  (List.range (timeBonds + 1)).flatMap fun time =>
    (combGaugeLinks width).map fun link =>
      { weight := 1
        time := time
        link := link }

/-- Literal polynomial sum of a finite weighted Cayley-Haar family. -/
def openCubeCayleyHaarJ2InsertionPolynomial
    (timeBonds width stage : Nat)
    (insertions : List OpenCubeCayleyHaarJ2Insertion) : RatPoly :=
  polySum (insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryCayleyHaarJ2Polynomial
        timeBonds width stage insertion.time insertion.link))

/-- Corresponding finite weighted sum of local Gram-triangle values. -/
def openCubeBulkCayleyHaarJ2FamilyTriangleSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (insertions : List OpenCubeCayleyHaarJ2Insertion) : Q' :=
  qListSum (insertions.map fun insertion =>
    insertion.weight *
      openCubeBulkCayleyHaarJ2TriangleSum
        timeBonds s hs stage leftTime rightTime
        insertion.time insertion.link)

private theorem qListSum_congr {A : Type} (f g : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → f item ≈ g item) →
    qListSum (items.map f) ≈ qListSum (items.map g)
  | [], _ => Q'.eqv_refl _
  | item :: items, h => Q'.add_eqv_congr' (h item List.mem_cons_self)
      (qListSum_congr f g items
        (fun other hother => h other (List.mem_cons_of_mem item hother)))

/-- Exact arbitrary-family consumer for Cayley-Haar `J2` insertions. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_cayleyHaarJ2_family_triangle
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q')
    (insertions : List OpenCubeCayleyHaarJ2Insertion) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
        (openCubeCayleyHaarJ2InsertionPolynomial
          timeBonds (bulkSourceWidth s) stage insertions) ≈
      openCubeBulkCayleyHaarJ2FamilyTriangleSum
        timeBonds s hs stage leftTime rightTime insertions := by
  let N := bulkSourceNoiseCount timeBonds s
  let left := bulkSourceHeronRadialSquare
    timeBonds s hs stage leftTime
  let right := bulkSourceHeronRadialSquare
    timeBonds s hs stage rightTime
  let insertionPolynomials := insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryCayleyHaarJ2Polynomial
        timeBonds (bulkSourceWidth s) stage
        insertion.time insertion.link)
  change finiteGaussianThirdCumulant N
      (finiteGaussianCenteredPolynomial leftOldCenter left)
      (finiteGaussianCenteredPolynomial rightOldCenter right)
      (polySum insertionPolynomials) ≈
    openCubeBulkCayleyHaarJ2FamilyTriangleSum
      timeBonds s hs stage leftTime rightTime insertions
  have hcenter := finiteGaussianThirdCumulant_center_left_middle N
    leftOldCenter rightOldCenter left right (polySum insertionPolynomials)
  have hsum := finiteGaussianThirdCumulant_polySum_right N left right
    insertionPolynomials
  have hterms : qListSum (insertionPolynomials.map fun polynomial =>
        finiteGaussianThirdCumulant N left right polynomial) ≈
      openCubeBulkCayleyHaarJ2FamilyTriangleSum
        timeBonds s hs stage leftTime rightTime insertions := by
    unfold insertionPolynomials openCubeBulkCayleyHaarJ2FamilyTriangleSum
    simp only [List.map_map]
    exact qListSum_congr _ _ insertions (fun insertion _ =>
      Q'.eqv_trans _ _ _
        (finiteGaussianThirdCumulant_smul_right N insertion.weight
          left right
          (combGaugeFreeHistoryCayleyHaarJ2Polynomial
            timeBonds (bulkSourceWidth s) stage
            insertion.time insertion.link))
        (Q'.mul_eqv_congr_left insertion.weight _ _
          (finiteGaussianThirdCumulant_openCube_bulk_cayleyHaarJ2_triangle
            timeBonds s hs stage leftTime rightTime
            insertion.time insertion.link)))
  exact Q'.eqv_trans _ _ _ hcenter (Q'.eqv_trans _ _ _ hsum hterms)

/-- Canonical complete reference Cayley-Haar insertion, retaining every
history slice and every comb-gauge edge. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeCayleyHaarJ2_triangle
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q') :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
        (openCubeCayleyHaarJ2InsertionPolynomial
          timeBonds (bulkSourceWidth s) stage
          (completeOpenCubeCayleyHaarJ2Insertions
            timeBonds (bulkSourceWidth s))) ≈
      openCubeBulkCayleyHaarJ2FamilyTriangleSum
        timeBonds s hs stage leftTime rightTime
        (completeOpenCubeCayleyHaarJ2Insertions
          timeBonds (bulkSourceWidth s)) :=
  finiteGaussianThirdCumulant_openCube_bulk_old_centered_cayleyHaarJ2_family_triangle
    timeBonds s hs stage leftTime rightTime leftOldCenter rightOldCenter
    (completeOpenCubeCayleyHaarJ2Insertions
      timeBonds (bulkSourceWidth s))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant.finiteGaussianCayleyHaarJ2Polynomial_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant.finiteGaussianThirdCumulant_openCube_bulk_cayleyHaarJ2_triangle
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyHaarCumulant.finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeCayleyHaarJ2_triangle
