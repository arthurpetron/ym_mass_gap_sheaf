/-
# Actual open-cube bulk-source/kinetic heat-action fourth cumulant

For two Cayley chart vectors `a,b` on adjacent history slices, the exact
temporal-gauge trace deficit is

  4*e^2*|a-b|^2 / ((1+e^2*|a|^2)*(1+e^2*|b|^2)).

Its complete fourth heat-action coefficient is therefore

  -|a-b|^2*(|a|^2+|b|^2)
    + |a-b|^4/3 - 2*|a-b|^2/3.

This leaf uses the SAME rooted-comb/Heron history coordinates as the checked
FREE precision.  It reduces the quartic part to `2+2+4` Wick sums and the
quadratic part to the checked three-square Gram triangle.  The canonical
family ranges over every temporal bond and every comb-gauge edge, so the two
endpoint bonds are retained rather than silently discarded.

This is still finite FREE reference-Gaussian algebra.  It does not include
the spatial-face, Haar, source-renormalization or ORIGINAL-law corrections,
and proves no sign, uniform estimate or physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Componentwise difference of two three-color Gaussian row triples. -/
def finiteGaussianKineticDifferenceRows
    (left right : Nat → Nat → Q') (component coordinate : Nat) : Q' :=
  left component coordinate + -(right component coordinate)

/-- Weighted four-row blocks representing a product of two three-color row
norms. -/
def finiteGaussianRowNormProductQuarticRowBlocks
    (weight : Q') (left right : Nat → Nat → Q') :
    List WeightedQuarticRowBlock :=
  (List.range 3).flatMap fun leftComponent =>
    (List.range 3).map fun rightComponent =>
      { weight := weight
        first := left leftComponent
        second := left leftComponent
        third := right rightComponent
        fourth := right rightComponent }

/-- Weighted row squares representing a three-color row norm. -/
def finiteGaussianWeightedRowNormSquares
    (weight : Q') (rows : Nat → Nat → Q') : List WeightedRowSquare :=
  (List.range 3).map fun component =>
    { weight := weight
      row := rows component }

private theorem polySmul_polySum (weight : Q') : ∀ polynomials : List RatPoly,
    RatPolyCoeffEqv (polySmul weight (polySum polynomials))
      (polySum (polynomials.map fun polynomial =>
        polySmul weight polynomial))
  | [] => RatPolyCoeffEqv.zero_smul polyZero
  | polynomial :: polynomials =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.smul_add weight polynomial (polySum polynomials))
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (polySmul_polySum weight polynomials))

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

/-- A weighted product of two literal three-color row norms is exactly the
corresponding nine weighted four-row blocks. -/
theorem finiteGaussianRowNormProductQuarticRowBlocks_coeffEqv
    (N : Nat) (weight : Q') (left right : Nat → Nat → Q') :
    RatPolyCoeffEqv
      (polySmul weight
        (polyMul
          (finiteGaussianRowDot N 3 left left)
          (finiteGaussianRowDot N 3 right right)))
      (weightedTermPolynomial
        ((finiteGaussianRowNormProductQuarticRowBlocks
          weight left right).map (weightedQuarticRowBlockTerm N))) := by
  let monomials := finiteGaussianRowDotQuarticMonomials N 3 3
    left left right right
  have hproduct := finiteGaussianRowDot_product_quarticMonomials N 3 3
    left left right right
  have hscaled := hproduct.smul weight
  have hsum := polySmul_polySum weight monomials
  exact RatPolyCoeffEqv.trans hscaled (RatPolyCoeffEqv.trans hsum (by
    unfold monomials finiteGaussianRowNormProductQuarticRowBlocks
      weightedTermPolynomial weightedQuarticRowBlockTerm
      finiteGaussianRowDotQuarticMonomials
    simp only [List.map_flatMap, List.map_map]
    exact RatPolyCoeffEqv.refl _))

/-- A weighted literal three-color row norm is exactly the corresponding
three weighted row squares. -/
theorem finiteGaussianWeightedRowNormSquares_coeffEqv
    (N : Nat) (weight : Q') (rows : Nat → Nat → Q') :
    RatPolyCoeffEqv
      (polySmul weight (finiteGaussianRowDot N 3 rows rows))
      (weightedTermPolynomial
        ((finiteGaussianWeightedRowNormSquares weight rows).map
          (weightedRowSquareTerm N))) := by
  let squares := (List.range 3).map fun component =>
    finiteGaussianRowSquare N (rows component)
  have hdot : RatPolyCoeffEqv
      (finiteGaussianRowDot N 3 rows rows) (polySum squares) := by
    unfold finiteGaussianRowDot squares finiteGaussianRowSquare
    exact RatPolyCoeffEqv.refl _
  have hsum := polySmul_polySum weight squares
  exact RatPolyCoeffEqv.trans (hdot.smul weight)
    (RatPolyCoeffEqv.trans hsum (by
      unfold squares finiteGaussianWeightedRowNormSquares
        weightedTermPolynomial weightedRowSquareTerm
      simp only [List.map_map]
      exact RatPolyCoeffEqv.refl _))

/-- Twenty-seven quartic blocks of
`-|a-b|^2*(|a|^2+|b|^2)+|a-b|^4/3`. -/
def finiteGaussianKineticFourthActionQuarticRowBlocks
    (left right : Nat → Nat → Q') : List WeightedQuarticRowBlock :=
  let difference := finiteGaussianKineticDifferenceRows left right
  finiteGaussianRowNormProductQuarticRowBlocks (-1) difference left ++
    (finiteGaussianRowNormProductQuarticRowBlocks (-1) difference right ++
      finiteGaussianRowNormProductQuarticRowBlocks
        spatialHeatOneThird difference difference)

/-- Three quadratic blocks of `-2*|a-b|^2/3`. -/
def finiteGaussianKineticFourthActionQuadraticRowSquares
    (left right : Nat → Nat → Q') : List WeightedRowSquare :=
  finiteGaussianWeightedRowNormSquares spatialHeatNegTwoThird
    (finiteGaussianKineticDifferenceRows left right)

/-- Literal quartic part of the kinetic fourth heat-action coefficient. -/
def finiteGaussianKineticFourthActionQuarticPolynomial
    (N : Nat) (left right : Nat → Nat → Q') : RatPoly :=
  weightedTermPolynomial
    ((finiteGaussianKineticFourthActionQuarticRowBlocks left right).map
      (weightedQuarticRowBlockTerm N))

/-- Literal quadratic part of the kinetic fourth heat-action coefficient. -/
def finiteGaussianKineticFourthActionQuadraticPolynomial
    (N : Nat) (left right : Nat → Nat → Q') : RatPoly :=
  weightedTermPolynomial
    ((finiteGaussianKineticFourthActionQuadraticRowSquares left right).map
      (weightedRowSquareTerm N))

/-- Literal complete kinetic fourth heat-action coefficient. -/
def finiteGaussianKineticFourthActionPolynomial
    (N : Nat) (left right : Nat → Nat → Q') : RatPoly :=
  polyAdd
    (finiteGaussianKineticFourthActionQuarticPolynomial N left right)
    (finiteGaussianKineticFourthActionQuadraticPolynomial N left right)

/-- The twenty-seven quartic blocks equal the exact quartic expression from
the two-link Cayley trace deficit. -/
theorem finiteGaussianKineticFourthActionQuarticPolynomial_coeffEqv
    (N : Nat) (left right : Nat → Nat → Q') :
    let difference := finiteGaussianKineticDifferenceRows left right
    RatPolyCoeffEqv
      (polyAdd
        (polySmul (-1)
          (polyMul
            (finiteGaussianRowDot N 3 difference difference)
            (finiteGaussianRowDot N 3 left left)))
        (polyAdd
          (polySmul (-1)
            (polyMul
              (finiteGaussianRowDot N 3 difference difference)
              (finiteGaussianRowDot N 3 right right)))
          (polySmul spatialHeatOneThird
            (polyMul
              (finiteGaussianRowDot N 3 difference difference)
              (finiteGaussianRowDot N 3 difference difference)))))
      (finiteGaussianKineticFourthActionQuarticPolynomial N left right) := by
  let difference := finiteGaussianKineticDifferenceRows left right
  let leftBlocks := finiteGaussianRowNormProductQuarticRowBlocks
    (-1) difference left
  let rightBlocks := finiteGaussianRowNormProductQuarticRowBlocks
    (-1) difference right
  let squareBlocks := finiteGaussianRowNormProductQuarticRowBlocks
    spatialHeatOneThird difference difference
  have hleft := finiteGaussianRowNormProductQuarticRowBlocks_coeffEqv
    N (-1) difference left
  have hright := finiteGaussianRowNormProductQuarticRowBlocks_coeffEqv
    N (-1) difference right
  have hsquare := finiteGaussianRowNormProductQuarticRowBlocks_coeffEqv
    N spatialHeatOneThird difference difference
  have hpieces := RatPolyCoeffEqv.add hleft
    (RatPolyCoeffEqv.add hright hsquare)
  have hrightAppend := weightedTermPolynomial_append
    (rightBlocks.map (weightedQuarticRowBlockTerm N))
    (squareBlocks.map (weightedQuarticRowBlockTerm N))
  have hallAppend := weightedTermPolynomial_append
    (leftBlocks.map (weightedQuarticRowBlockTerm N))
    ((rightBlocks ++ squareBlocks).map (weightedQuarticRowBlockTerm N))
  exact RatPolyCoeffEqv.trans hpieces
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) hrightAppend)
      (by
        simpa only [List.map_append] using hallAppend))

/-- The three quadratic blocks equal the exact quadratic term from the
two-link heat-action expansion. -/
theorem finiteGaussianKineticFourthActionQuadraticPolynomial_coeffEqv
    (N : Nat) (left right : Nat → Nat → Q') :
    RatPolyCoeffEqv
      (polySmul spatialHeatNegTwoThird
        (finiteGaussianRowDot N 3
          (finiteGaussianKineticDifferenceRows left right)
          (finiteGaussianKineticDifferenceRows left right)))
      (finiteGaussianKineticFourthActionQuadraticPolynomial
        N left right) :=
  finiteGaussianWeightedRowNormSquares_coeffEqv N
    spatialHeatNegTwoThird (finiteGaussianKineticDifferenceRows left right)

/-- Three-color Heron-pulled rows of one comb-gauge edge on one history
slice. -/
def combGaugeFreeHistoryHeronKineticSliceRows
    (timeBonds width stage time : Nat) (link : Z4Link) :
    Nat → Nat → Q' :=
  combGaugeFreeHistoryHeronDirectedLinkRows
    timeBonds width stage time 1 link

/-- Three-color forward-difference rows on one temporal bond. -/
def combGaugeFreeHistoryHeronKineticDifferenceRows
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    Nat → Nat → Q' :=
  finiteGaussianKineticDifferenceRows
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)

/-- Actual twenty-seven quartic blocks on one temporal bond and comb-gauge
edge. -/
def openCubeKineticFourthActionQuarticRowBlocks
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    List WeightedQuarticRowBlock :=
  finiteGaussianKineticFourthActionQuarticRowBlocks
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)

/-- Actual three quadratic blocks on one temporal bond and comb-gauge edge. -/
def openCubeKineticFourthActionQuadraticRowSquares
    (timeBonds width stage bond : Nat) (link : Z4Link) :
    List WeightedRowSquare :=
  finiteGaussianKineticFourthActionQuadraticRowSquares
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)

/-- Literal complete kinetic fourth-action polynomial on one actual temporal
bond and comb-gauge edge. -/
def combGaugeFreeHistoryKineticFourthActionPolynomial
    (timeBonds width stage bond : Nat) (link : Z4Link) : RatPoly :=
  finiteGaussianKineticFourthActionPolynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage bond link)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds width stage (bond + 1) link)

/-- Exact quartic Wick sum for two actual bulk-source times and one actual
kinetic bond/edge insertion. -/
def openCubeBulkKineticFourthActionQuarticWickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime bond : Nat) (link : Z4Link) : Q' :=
  finiteGaussianWeightedRowBlocksWickSum
    (bulkSourceNoiseCount timeBonds s)
    (bulkSourceHeronQuadraticRowBlocks timeBonds s hs stage leftTime)
    (bulkSourceHeronQuadraticRowBlocks timeBonds s hs stage rightTime)
    (openCubeKineticFourthActionQuarticRowBlocks
      timeBonds (bulkSourceWidth s) stage bond link)

/-- Exact quadratic Gram-triangle sum for two actual bulk-source times and one
actual kinetic bond/edge insertion. -/
def openCubeBulkKineticFourthActionQuadraticTriangleSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime bond : Nat) (link : Z4Link) : Q' :=
  finiteGaussianWeightedRowSquaresTriangleSum
    (bulkSourceNoiseCount timeBonds s)
    (bulkSourceHeronWeightedRowSquares timeBonds s hs stage leftTime)
    (bulkSourceHeronWeightedRowSquares timeBonds s hs stage rightTime)
    (openCubeKineticFourthActionQuadraticRowSquares
      timeBonds (bulkSourceWidth s) stage bond link)

/-- Complete one-bond/edge kinetic fourth-action Wick value. -/
def openCubeBulkKineticFourthActionWickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime bond : Nat) (link : Z4Link) : Q' :=
  openCubeBulkKineticFourthActionQuarticWickSum
      timeBonds s hs stage leftTime rightTime bond link +
    openCubeBulkKineticFourthActionQuadraticTriangleSum
      timeBonds s hs stage leftTime rightTime bond link

/-- The complete kinetic fourth-action insertion on one actual temporal bond
and comb-gauge edge reduces to the displayed finite Wick/Gram value. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_kineticFourthAction_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime bond : Nat) (link : Z4Link) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
        (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
        (combGaugeFreeHistoryKineticFourthActionPolynomial
          timeBonds (bulkSourceWidth s) stage bond link) ≈
      openCubeBulkKineticFourthActionWickSum
        timeBonds s hs stage leftTime rightTime bond link := by
  let N := bulkSourceNoiseCount timeBonds s
  let left := bulkSourceHeronRadialSquare
    timeBonds s hs stage leftTime
  let right := bulkSourceHeronRadialSquare
    timeBonds s hs stage rightTime
  let leftBlocks := bulkSourceHeronQuadraticRowBlocks
    timeBonds s hs stage leftTime
  let rightBlocks := bulkSourceHeronQuadraticRowBlocks
    timeBonds s hs stage rightTime
  let insertionBlocks := openCubeKineticFourthActionQuarticRowBlocks
    timeBonds (bulkSourceWidth s) stage bond link
  let leftSquares := bulkSourceHeronWeightedRowSquares
    timeBonds s hs stage leftTime
  let rightSquares := bulkSourceHeronWeightedRowSquares
    timeBonds s hs stage rightTime
  let insertionSquares := openCubeKineticFourthActionQuadraticRowSquares
    timeBonds (bulkSourceWidth s) stage bond link
  let quartic := finiteGaussianKineticFourthActionQuarticPolynomial N
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds (bulkSourceWidth s) stage bond link)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds (bulkSourceWidth s) stage (bond + 1) link)
  let quadratic := finiteGaussianKineticFourthActionQuadraticPolynomial N
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds (bulkSourceWidth s) stage bond link)
    (combGaugeFreeHistoryHeronKineticSliceRows
      timeBonds (bulkSourceWidth s) stage (bond + 1) link)
  have hquartic : finiteGaussianThirdCumulant N left right quartic ≈
      finiteGaussianWeightedRowBlocksWickSum
        N leftBlocks rightBlocks insertionBlocks := by
    unfold left right
    rw [bulkSourceHeronRadialSquare_eq_quadraticTerms,
      bulkSourceHeronRadialSquare_eq_quadraticTerms,
      bulkSourceHeronQuadraticTerms_eq_rowBlocks,
      bulkSourceHeronQuadraticTerms_eq_rowBlocks]
    exact finiteGaussianThirdCumulant_weighted_row_blocks_wick
      N leftBlocks rightBlocks insertionBlocks
  have hquadratic : finiteGaussianThirdCumulant N left right quadratic ≈
      finiteGaussianWeightedRowSquaresTriangleSum
        N leftSquares rightSquares insertionSquares := by
    unfold left right
    rw [bulkSourceHeronRadialSquare_eq_weightedRowSquares,
      bulkSourceHeronRadialSquare_eq_weightedRowSquares]
    exact finiteGaussianThirdCumulant_weighted_row_squares_triangle
      N leftSquares rightSquares insertionSquares
  have hsplit := finiteGaussianThirdCumulant_add_right N left right
    quartic quadratic
  unfold combGaugeFreeHistoryKineticFourthActionPolynomial
    finiteGaussianKineticFourthActionPolynomial
    openCubeBulkKineticFourthActionWickSum
    openCubeBulkKineticFourthActionQuarticWickSum
    openCubeBulkKineticFourthActionQuadraticTriangleSum
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr' hquartic hquadratic)

/-- Arbitrary scalar OLD centers cancel inside the connected kinetic
fourth-action insertion. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_kineticFourthAction_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime bond : Nat) (link : Z4Link)
    (leftOldCenter rightOldCenter : Q') :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
        (combGaugeFreeHistoryKineticFourthActionPolynomial
          timeBonds (bulkSourceWidth s) stage bond link) ≈
      openCubeBulkKineticFourthActionWickSum
        timeBonds s hs stage leftTime rightTime bond link :=
  Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_center_left_middle
      (bulkSourceNoiseCount timeBonds s) leftOldCenter rightOldCenter
      (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
      (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
      (combGaugeFreeHistoryKineticFourthActionPolynomial
        timeBonds (bulkSourceWidth s) stage bond link))
    (finiteGaussianThirdCumulant_openCube_bulk_kineticFourthAction_wick
      timeBonds s hs stage leftTime rightTime bond link)

/-- One weighted kinetic fourth-action insertion. -/
structure OpenCubeKineticFourthActionInsertion where
  weight : Q'
  bond : Nat
  link : Z4Link

/-- Canonical kinetic insertion list: every forward temporal bond and every
comb-gauge edge, including the two endpoint bonds when `timeBonds > 0`. -/
def completeOpenCubeKineticFourthActionInsertions
    (timeBonds width : Nat) : List OpenCubeKineticFourthActionInsertion :=
  (List.range timeBonds).flatMap fun bond =>
    (combGaugeLinks width).map fun link =>
      { weight := 1
        bond := bond
        link := link }

/-- Literal polynomial sum of a finite weighted kinetic insertion family. -/
def openCubeKineticFourthActionInsertionPolynomial
    (timeBonds width stage : Nat)
    (insertions : List OpenCubeKineticFourthActionInsertion) : RatPoly :=
  polySum (insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryKineticFourthActionPolynomial
        timeBonds width stage insertion.bond insertion.link))

/-- Corresponding finite weighted sum of one-bond/edge Wick values. -/
def openCubeBulkKineticFourthActionFamilyWickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (insertions : List OpenCubeKineticFourthActionInsertion) : Q' :=
  qListSum (insertions.map fun insertion =>
    insertion.weight *
      openCubeBulkKineticFourthActionWickSum
        timeBonds s hs stage leftTime rightTime
        insertion.bond insertion.link)

private theorem qListSum_congr {A : Type} (f g : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → f item ≈ g item) →
    qListSum (items.map f) ≈ qListSum (items.map g)
  | [], _ => Q'.eqv_refl _
  | item :: items, h => Q'.add_eqv_congr' (h item List.mem_cons_self)
      (qListSum_congr f g items
        (fun other hother => h other (List.mem_cons_of_mem item hother)))

/-- Exact arbitrary-family consumer for kinetic fourth-action insertions. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_kineticFourthAction_family_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q')
    (insertions : List OpenCubeKineticFourthActionInsertion) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
        (openCubeKineticFourthActionInsertionPolynomial
          timeBonds (bulkSourceWidth s) stage insertions) ≈
      openCubeBulkKineticFourthActionFamilyWickSum
        timeBonds s hs stage leftTime rightTime insertions := by
  let N := bulkSourceNoiseCount timeBonds s
  let left := bulkSourceHeronRadialSquare
    timeBonds s hs stage leftTime
  let right := bulkSourceHeronRadialSquare
    timeBonds s hs stage rightTime
  let insertionPolynomials := insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryKineticFourthActionPolynomial
        timeBonds (bulkSourceWidth s) stage
        insertion.bond insertion.link)
  change finiteGaussianThirdCumulant N
      (finiteGaussianCenteredPolynomial leftOldCenter left)
      (finiteGaussianCenteredPolynomial rightOldCenter right)
      (polySum insertionPolynomials) ≈
    openCubeBulkKineticFourthActionFamilyWickSum
      timeBonds s hs stage leftTime rightTime insertions
  have hcenter := finiteGaussianThirdCumulant_center_left_middle N
    leftOldCenter rightOldCenter left right (polySum insertionPolynomials)
  have hsum := finiteGaussianThirdCumulant_polySum_right N left right
    insertionPolynomials
  have hterms : qListSum (insertionPolynomials.map fun polynomial =>
        finiteGaussianThirdCumulant N left right polynomial) ≈
      openCubeBulkKineticFourthActionFamilyWickSum
        timeBonds s hs stage leftTime rightTime insertions := by
    unfold insertionPolynomials openCubeBulkKineticFourthActionFamilyWickSum
    simp only [List.map_map]
    exact qListSum_congr _ _ insertions (fun insertion _ =>
      Q'.eqv_trans _ _ _
        (finiteGaussianThirdCumulant_smul_right N insertion.weight
          left right
          (combGaugeFreeHistoryKineticFourthActionPolynomial
            timeBonds (bulkSourceWidth s) stage
            insertion.bond insertion.link))
        (Q'.mul_eqv_congr_left insertion.weight _ _
          (finiteGaussianThirdCumulant_openCube_bulk_kineticFourthAction_wick
            timeBonds s hs stage leftTime rightTime
            insertion.bond insertion.link)))
  exact Q'.eqv_trans _ _ _ hcenter (Q'.eqv_trans _ _ _ hsum hterms)

/-- Canonical complete kinetic family, retaining every temporal bond and every
comb-gauge edge on the finite open-cube history. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeKineticFourthAction_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q') :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
        (openCubeKineticFourthActionInsertionPolynomial
          timeBonds (bulkSourceWidth s) stage
          (completeOpenCubeKineticFourthActionInsertions
            timeBonds (bulkSourceWidth s))) ≈
      openCubeBulkKineticFourthActionFamilyWickSum
        timeBonds s hs stage leftTime rightTime
        (completeOpenCubeKineticFourthActionInsertions
          timeBonds (bulkSourceWidth s)) :=
  finiteGaussianThirdCumulant_openCube_bulk_old_centered_kineticFourthAction_family_wick
    timeBonds s hs stage leftTime rightTime leftOldCenter rightOldCenter
    (completeOpenCubeKineticFourthActionInsertions
      timeBonds (bulkSourceWidth s))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant.finiteGaussianRowNormProductQuarticRowBlocks_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant.finiteGaussianKineticFourthActionQuarticPolynomial_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant.finiteGaussianKineticFourthActionQuadraticPolynomial_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant.finiteGaussianThirdCumulant_openCube_bulk_kineticFourthAction_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkKineticHeatActionCumulant.finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeKineticFourthAction_wick
