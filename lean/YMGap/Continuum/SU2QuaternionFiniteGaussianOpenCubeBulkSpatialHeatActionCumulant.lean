/-
# Actual open-cube bulk-source/spatial heat-action fourth cumulant

For one zero-winding spatial plaquette the complete fourth action coefficient
is

  F4/4 + F2^2/48 - F2/6,

where the exact Cayley quadratic coefficient is `F2 = 4*|B|^2` and `B` is
the directed sum of the four plaquette slots.  Thus the two terms not covered
by the normalized `F4` leaf are `|B|^4/3` and `-2*|B|^2/3`.

This leaf joins all three pieces against the two literal open-cube bulk-source
quadratics.  The `F4/4` and `F2^2/48` pieces reduce to checked `2+2+4` Wick
sums.  The `-F2/6` piece reduces to the checked Gram triangle for three row
squares.  Arbitrary scalar OLD centers and arbitrary finite face/time weights
are retained.

The theorem is only the finite FREE reference-Gaussian spatial-face
coefficient.  It does not include kinetic, Haar, terminal-history, higher
remainder or ORIGINAL-law terms, and it proves no sign, uniform bound or
physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
import YMGap.Continuum.SU2QuaternionFiniteGaussianThreeSquareThirdCumulant

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeSquareThirdCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant

local infix:50 " ≈ " => Q'.eqv

/-- Exact coefficient `1/4` of the normalized Cayley quartic. -/
def spatialHeatQuarter : Q' := Q'.mkPos 1 4 (by decide)

/-- Exact coefficient `1/3` of `|B|^4 = F2^2/16`. -/
def spatialHeatOneThird : Q' := Q'.mkPos 1 3 (by decide)

/-- Exact coefficient `-2/3` of `|B|^2 = F2/4`. -/
def spatialHeatNegTwoThird : Q' := Q'.mkPos (-2) 3 (by decide)

/-- A rationally weighted literal Gaussian row square. -/
structure WeightedRowSquare where
  weight : Q'
  row : Nat → Q'

def weightedRowSquareTerm (N : Nat)
    (term : WeightedRowSquare) : Q' × RatPoly :=
  (term.weight, finiteGaussianRowSquare N term.row)

private theorem qListSum_congr {A : Type} (f g : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → f item ≈ g item) →
    qListSum (items.map f) ≈ qListSum (items.map g)
  | [], _ => Q'.eqv_refl _
  | item :: items, h => Q'.add_eqv_congr' (h item List.mem_cons_self)
      (qListSum_congr f g items
        (fun other hother => h other (List.mem_cons_of_mem item hother)))

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

/-- Explicit finite sum of the Gram-triangle values for three weighted row
squares. -/
def finiteGaussianWeightedRowSquaresTriangleSum
    (N : Nat)
    (left right insertions : List WeightedRowSquare) : Q' :=
  qListSum (left.map fun leftTerm =>
    qListSum (right.map fun rightTerm =>
      qListSum (insertions.map fun insertionTerm =>
        leftTerm.weight * (rightTerm.weight *
          (insertionTerm.weight *
            (8 * finiteRowGram N leftTerm.row rightTerm.row *
              finiteRowGram N leftTerm.row insertionTerm.row *
              finiteRowGram N rightTerm.row insertionTerm.row))))))

/-- Weighted sums of literal row squares reduce term-by-term to the checked
three-square Gram triangle. -/
theorem finiteGaussianThirdCumulant_weighted_row_squares_triangle
    (N : Nat)
    (left right insertions : List WeightedRowSquare) :
    finiteGaussianThirdCumulant N
        (weightedTermPolynomial (left.map (weightedRowSquareTerm N)))
        (weightedTermPolynomial (right.map (weightedRowSquareTerm N)))
        (weightedTermPolynomial (insertions.map (weightedRowSquareTerm N))) ≈
      finiteGaussianWeightedRowSquaresTriangleSum N left right insertions := by
  have hsum := finiteGaussianThirdCumulant_weighted_polySum_three N
    (left.map (weightedRowSquareTerm N))
    (right.map (weightedRowSquareTerm N))
    (insertions.map (weightedRowSquareTerm N))
  exact Q'.eqv_trans _ _ _ hsum (by
    simp only [List.map_map]
    exact qListSum_congr _ _ left (fun leftTerm _ =>
      qListSum_congr _ _ right (fun rightTerm _ =>
        qListSum_congr _ _ insertions (fun insertionTerm _ =>
          Q'.mul_eqv_congr_left leftTerm.weight _ _
            (Q'.mul_eqv_congr_left rightTerm.weight _ _
              (Q'.mul_eqv_congr_left insertionTerm.weight _ _
                (finiteGaussianThirdCumulant_three_row_squares N
                  leftTerm.row rightTerm.row insertionTerm.row)))))))

/-- Weighted row squares of one literal open-cube bulk source. -/
def bulkSourceHeronWeightedRowSquares
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) :
    List WeightedRowSquare :=
  (List.range (3 * (bulkSourceFaces s).length)).map fun rowIndex =>
    { weight := bulkSourceIndexWeight s hs (rowIndex / 3)
      row := bulkSourceHeronColorCurlRow timeBonds s stage time rowIndex }

theorem bulkSourceHeronRadialSquare_eq_weightedRowSquares
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) :
    bulkSourceHeronRadialSquare timeBonds s hs stage time =
      weightedTermPolynomial
        ((bulkSourceHeronWeightedRowSquares
          timeBonds s hs stage time).map
            (weightedRowSquareTerm (bulkSourceNoiseCount timeBonds s))) := by
  unfold bulkSourceHeronRadialSquare
    bulkSourceHeronWeightedRowSquares weightedRowSquareTerm
    weightedTermPolynomial bulkSourceNoiseCount
    combGaugeFreeHistoryHeronWeightedCurlRadialSquare
    finiteGaussianWeightedRadialSquare
  simp only [List.map_map]
  rfl

/-- Nine quartic row blocks of the exact `F2^2/48 = |B|^4/3` face term. -/
def finiteGaussianCayleyH2SquareActionRowBlocks
    (a b c d : Nat → Nat → Q') : List WeightedQuarticRowBlock :=
  let slots := gaussianCayleySlot a b c d
  let totalRows := gaussianCayleyTotalRows slots
  (List.range 3).flatMap fun leftComponent =>
    (List.range 3).map fun rightComponent =>
      { weight := spatialHeatOneThird
        first := totalRows leftComponent
        second := totalRows leftComponent
        third := totalRows rightComponent
        fourth := totalRows rightComponent }

/-- Three quadratic row squares of the exact `-F2/6 = -2|B|^2/3` face
term. -/
def finiteGaussianCayleyH2ActionRowSquares
    (a b c d : Nat → Nat → Q') : List WeightedRowSquare :=
  let slots := gaussianCayleySlot a b c d
  let totalRows := gaussianCayleyTotalRows slots
  (List.range 3).map fun component =>
    { weight := spatialHeatNegTwoThird
      row := totalRows component }

/-- Literal polynomial for the `F2^2/48` spatial face-action term. -/
def finiteGaussianCayleyH2SquareActionPolynomial (N : Nat)
    (a b c d : Nat → Nat → Q') : RatPoly :=
  weightedTermPolynomial
    ((finiteGaussianCayleyH2SquareActionRowBlocks a b c d).map
      (weightedQuarticRowBlockTerm N))

/-- Literal polynomial for the `-F2/6` spatial face-action term. -/
def finiteGaussianCayleyH2ActionPolynomial (N : Nat)
    (a b c d : Nat → Nat → Q') : RatPoly :=
  weightedTermPolynomial
    ((finiteGaussianCayleyH2ActionRowSquares a b c d).map
      (weightedRowSquareTerm N))

/-- The nine quartic blocks are coefficientwise exactly
`(1/3)*|B|^4 = F2^2/48`. -/
theorem finiteGaussianCayleyH2SquareActionPolynomial_coeffEqv
    (N : Nat) (a b c d : Nat → Nat → Q') :
    RatPolyCoeffEqv
      (polySmul spatialHeatOneThird
        (polyMul
          (finiteGaussianRowDot N 3
            (gaussianCayleyTotalRows (gaussianCayleySlot a b c d))
            (gaussianCayleyTotalRows (gaussianCayleySlot a b c d)))
          (finiteGaussianRowDot N 3
            (gaussianCayleyTotalRows (gaussianCayleySlot a b c d))
            (gaussianCayleyTotalRows (gaussianCayleySlot a b c d)))))
      (finiteGaussianCayleyH2SquareActionPolynomial N a b c d) := by
  let slots := gaussianCayleySlot a b c d
  let totalRows := gaussianCayleyTotalRows slots
  let monomials := finiteGaussianRowDotQuarticMonomials N 3 3
    totalRows totalRows totalRows totalRows
  have hproduct := finiteGaussianRowDot_product_quarticMonomials N 3 3
    totalRows totalRows totalRows totalRows
  have hscaled := hproduct.smul spatialHeatOneThird
  have hsum := polySmul_polySum spatialHeatOneThird monomials
  exact RatPolyCoeffEqv.trans hscaled (RatPolyCoeffEqv.trans hsum (by
    unfold monomials finiteGaussianCayleyH2SquareActionPolynomial
      finiteGaussianCayleyH2SquareActionRowBlocks
      weightedTermPolynomial weightedQuarticRowBlockTerm
      finiteGaussianRowDotQuarticMonomials
    simp only [List.map_flatMap, List.map_map]
    exact RatPolyCoeffEqv.refl _))

/-- The three quadratic blocks are coefficientwise exactly
`(-2/3)*|B|^2 = -F2/6`. -/
theorem finiteGaussianCayleyH2ActionPolynomial_coeffEqv
    (N : Nat) (a b c d : Nat → Nat → Q') :
    RatPolyCoeffEqv
      (polySmul spatialHeatNegTwoThird
        (finiteGaussianRowDot N 3
          (gaussianCayleyTotalRows (gaussianCayleySlot a b c d))
          (gaussianCayleyTotalRows (gaussianCayleySlot a b c d))))
      (finiteGaussianCayleyH2ActionPolynomial N a b c d) := by
  let slots := gaussianCayleySlot a b c d
  let totalRows := gaussianCayleyTotalRows slots
  let squares := (List.range 3).map fun component =>
    finiteGaussianRowSquare N (totalRows component)
  change RatPolyCoeffEqv
    (polySmul spatialHeatNegTwoThird
      (finiteGaussianRowDot N 3 totalRows totalRows))
    (finiteGaussianCayleyH2ActionPolynomial N a b c d)
  have hdot : RatPolyCoeffEqv
      (finiteGaussianRowDot N 3 totalRows totalRows)
      (polySum squares) := by
    unfold finiteGaussianRowDot squares finiteGaussianRowSquare
    exact RatPolyCoeffEqv.refl _
  have hsum := polySmul_polySum spatialHeatNegTwoThird squares
  exact RatPolyCoeffEqv.trans (hdot.smul spatialHeatNegTwoThird)
    (RatPolyCoeffEqv.trans hsum (by
      unfold squares finiteGaussianCayleyH2ActionPolynomial
        finiteGaussianCayleyH2ActionRowSquares weightedTermPolynomial
        weightedRowSquareTerm
      simp only [List.map_map]
      exact RatPolyCoeffEqv.refl _))

/-- Literal complete fourth spatial heat-action coefficient
`F4/4 + F2^2/48 - F2/6` for arbitrary finite rational rows. -/
def finiteGaussianSpatialHeatActionFourthPolynomial (N : Nat)
    (a b c d : Nat → Nat → Q') : RatPoly :=
  polyAdd
    (polySmul spatialHeatQuarter
      (finiteGaussianNormalizedCayleyH4Polynomial N a b c d))
    (polyAdd
      (finiteGaussianCayleyH2SquareActionPolynomial N a b c d)
      (finiteGaussianCayleyH2ActionPolynomial N a b c d))

/-- The same complete coefficient on one actual rooted-comb/Heron open-cube
plaquette. -/
def combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
    (timeBonds width stage time : Nat) (face : Z4Plaq) : RatPoly :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianSpatialHeatActionFourthPolynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Actual `F2^2/48` row blocks on one open-cube plaquette. -/
def openCubePlaquetteH2SquareActionRowBlocks
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedQuarticRowBlock :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianCayleyH2SquareActionRowBlocks
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Actual `-F2/6` row squares on one open-cube plaquette. -/
def openCubePlaquetteH2ActionRowSquares
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedRowSquare :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianCayleyH2ActionRowSquares
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Exact `F2^2/48` Wick sum for two actual bulk-source times and one actual
plaquette. -/
def openCubeBulkPlaquetteH2SquareActionWickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq) : Q' :=
  finiteGaussianWeightedRowBlocksWickSum
    (bulkSourceNoiseCount timeBonds s)
    (bulkSourceHeronQuadraticRowBlocks timeBonds s hs stage leftTime)
    (bulkSourceHeronQuadraticRowBlocks timeBonds s hs stage rightTime)
    (openCubePlaquetteH2SquareActionRowBlocks
      timeBonds (bulkSourceWidth s) stage insertionTime face)

/-- Exact `-F2/6` Gram-triangle sum for two actual bulk-source times and one
actual plaquette. -/
def openCubeBulkPlaquetteH2ActionTriangleSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq) : Q' :=
  finiteGaussianWeightedRowSquaresTriangleSum
    (bulkSourceNoiseCount timeBonds s)
    (bulkSourceHeronWeightedRowSquares timeBonds s hs stage leftTime)
    (bulkSourceHeronWeightedRowSquares timeBonds s hs stage rightTime)
    (openCubePlaquetteH2ActionRowSquares
      timeBonds (bulkSourceWidth s) stage insertionTime face)

/-- The `F2^2/48` insertion against two literal bulk-source observables is
the displayed finite weighted `2+2+4` Wick sum. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_H2SquareAction_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
        (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
        (let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
          timeBonds (bulkSourceWidth s) stage insertionTime face
        finiteGaussianCayleyH2SquareActionPolynomial
          (bulkSourceNoiseCount timeBonds s)
          (rows 0) (rows 1) (rows 2) (rows 3)) ≈
      openCubeBulkPlaquetteH2SquareActionWickSum
        timeBonds s hs stage leftTime rightTime insertionTime face := by
  let N := bulkSourceNoiseCount timeBonds s
  let leftBlocks := bulkSourceHeronQuadraticRowBlocks
    timeBonds s hs stage leftTime
  let rightBlocks := bulkSourceHeronQuadraticRowBlocks
    timeBonds s hs stage rightTime
  let insertionBlocks := openCubePlaquetteH2SquareActionRowBlocks
    timeBonds (bulkSourceWidth s) stage insertionTime face
  rw [bulkSourceHeronRadialSquare_eq_quadraticTerms,
    bulkSourceHeronRadialSquare_eq_quadraticTerms,
    bulkSourceHeronQuadraticTerms_eq_rowBlocks,
    bulkSourceHeronQuadraticTerms_eq_rowBlocks]
  change finiteGaussianThirdCumulant N
      (weightedTermPolynomial
        (leftBlocks.map (weightedQuadraticRowBlockTerm N)))
      (weightedTermPolynomial
        (rightBlocks.map (weightedQuadraticRowBlockTerm N)))
      (weightedTermPolynomial
        (insertionBlocks.map (weightedQuarticRowBlockTerm N))) ≈
    finiteGaussianWeightedRowBlocksWickSum
      N leftBlocks rightBlocks insertionBlocks
  exact finiteGaussianThirdCumulant_weighted_row_blocks_wick
    N leftBlocks rightBlocks insertionBlocks

/-- The `-F2/6` insertion against two literal bulk-source observables is the
displayed finite weighted sum of Gram triangles. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_H2Action_triangle
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
        (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
        (let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
          timeBonds (bulkSourceWidth s) stage insertionTime face
        finiteGaussianCayleyH2ActionPolynomial
          (bulkSourceNoiseCount timeBonds s)
          (rows 0) (rows 1) (rows 2) (rows 3)) ≈
      openCubeBulkPlaquetteH2ActionTriangleSum
        timeBonds s hs stage leftTime rightTime insertionTime face := by
  let N := bulkSourceNoiseCount timeBonds s
  let leftSquares := bulkSourceHeronWeightedRowSquares
    timeBonds s hs stage leftTime
  let rightSquares := bulkSourceHeronWeightedRowSquares
    timeBonds s hs stage rightTime
  let insertionSquares := openCubePlaquetteH2ActionRowSquares
    timeBonds (bulkSourceWidth s) stage insertionTime face
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

/-- Exact complete spatial-face fourth-action Wick value. -/
def openCubeBulkPlaquetteSpatialHeatActionFourthWickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq) : Q' :=
  spatialHeatQuarter *
      openCubeBulkPlaquetteNormalizedH4WickSum
        timeBonds s hs stage leftTime rightTime insertionTime face +
    (openCubeBulkPlaquetteH2SquareActionWickSum
        timeBonds s hs stage leftTime rightTime insertionTime face +
      openCubeBulkPlaquetteH2ActionTriangleSum
        timeBonds s hs stage leftTime rightTime insertionTime face)

/-- The third cumulant of two literal bulk-source observables and the complete
one-face coefficient `F4/4 + F2^2/48 - F2/6` is exactly the displayed finite
Wick/Gram sum. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_spatialHeatActionFourth_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
        (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
        (combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
          timeBonds (bulkSourceWidth s) stage insertionTime face) ≈
      openCubeBulkPlaquetteSpatialHeatActionFourthWickSum
        timeBonds s hs stage leftTime rightTime insertionTime face := by
  let N := bulkSourceNoiseCount timeBonds s
  let left := bulkSourceHeronRadialSquare
    timeBonds s hs stage leftTime
  let right := bulkSourceHeronRadialSquare
    timeBonds s hs stage rightTime
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds (bulkSourceWidth s) stage insertionTime face
  let f4 := finiteGaussianNormalizedCayleyH4Polynomial
    N (rows 0) (rows 1) (rows 2) (rows 3)
  let h2square := finiteGaussianCayleyH2SquareActionPolynomial
    N (rows 0) (rows 1) (rows 2) (rows 3)
  let h2 := finiteGaussianCayleyH2ActionPolynomial
    N (rows 0) (rows 1) (rows 2) (rows 3)
  have hsplit := finiteGaussianThirdCumulant_add_right N left right
    (polySmul spatialHeatQuarter f4) (polyAdd h2square h2)
  have hf4 := Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_smul_right N spatialHeatQuarter
      left right f4)
    (Q'.mul_eqv_congr_left spatialHeatQuarter _ _
      (finiteGaussianThirdCumulant_openCube_bulk_normalizedH4_wick
        timeBonds s hs stage leftTime rightTime insertionTime face))
  have hrest := Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_add_right N left right h2square h2)
    (Q'.add_eqv_congr'
      (finiteGaussianThirdCumulant_openCube_bulk_H2SquareAction_wick
        timeBonds s hs stage leftTime rightTime insertionTime face)
      (finiteGaussianThirdCumulant_openCube_bulk_H2Action_triangle
        timeBonds s hs stage leftTime rightTime insertionTime face))
  unfold combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
    finiteGaussianSpatialHeatActionFourthPolynomial
    openCubeBulkPlaquetteSpatialHeatActionFourthWickSum
  exact Q'.eqv_trans _ _ _ hsplit (Q'.add_eqv_congr' hf4 hrest)

/-- Arbitrary scalar OLD centers cancel from the connected complete
spatial-face fourth-action insertion. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_spatialHeatActionFourth_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq)
    (leftOldCenter rightOldCenter : Q') :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
        (combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
          timeBonds (bulkSourceWidth s) stage insertionTime face) ≈
      openCubeBulkPlaquetteSpatialHeatActionFourthWickSum
        timeBonds s hs stage leftTime rightTime insertionTime face :=
  Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_center_left_middle
      (bulkSourceNoiseCount timeBonds s) leftOldCenter rightOldCenter
      (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
      (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
      (combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
        timeBonds (bulkSourceWidth s) stage insertionTime face))
    (finiteGaussianThirdCumulant_openCube_bulk_spatialHeatActionFourth_wick
      timeBonds s hs stage leftTime rightTime insertionTime face)

/-- One weighted complete spatial-face fourth-action insertion. -/
structure OpenCubeSpatialHeatActionFourthInsertion where
  weight : Q'
  time : Nat
  face : Z4Plaq

/-- Literal polynomial sum of a finite weighted complete spatial-face
insertion family. -/
def openCubeSpatialHeatActionFourthInsertionPolynomial
    (timeBonds width stage : Nat)
    (insertions : List OpenCubeSpatialHeatActionFourthInsertion) : RatPoly :=
  polySum (insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
        timeBonds width stage insertion.time insertion.face))

/-- Corresponding finite weighted sum of complete one-face Wick values. -/
def openCubeBulkPlaquetteSpatialHeatActionFourthFamilyWickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (insertions : List OpenCubeSpatialHeatActionFourthInsertion) : Q' :=
  qListSum (insertions.map fun insertion =>
    insertion.weight *
      openCubeBulkPlaquetteSpatialHeatActionFourthWickSum
        timeBonds s hs stage leftTime rightTime
        insertion.time insertion.face)

/-- Literal OLD-centered finite Gaussian response to a weighted family of
complete spatial-face fourth-action insertions. -/
def openCubeBulkOldCenteredSpatialHeatActionFourthFamilyCumulant
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q')
    (insertions : List OpenCubeSpatialHeatActionFourthInsertion) : Q' :=
  finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
    (finiteGaussianCenteredPolynomial leftOldCenter
      (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
    (finiteGaussianCenteredPolynomial rightOldCenter
      (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
    (openCubeSpatialHeatActionFourthInsertionPolynomial
      timeBonds (bulkSourceWidth s) stage insertions)

/-- Exact finite-family consumer for the complete spatial-face fourth-action
coefficient, with arbitrary scalar OLD centers and rational insertion
weights. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_spatialHeatActionFourth_family_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q')
    (insertions : List OpenCubeSpatialHeatActionFourthInsertion) :
    openCubeBulkOldCenteredSpatialHeatActionFourthFamilyCumulant
        timeBonds s hs stage leftTime rightTime
        leftOldCenter rightOldCenter insertions ≈
      openCubeBulkPlaquetteSpatialHeatActionFourthFamilyWickSum
        timeBonds s hs stage leftTime rightTime insertions := by
  let N := bulkSourceNoiseCount timeBonds s
  let left := bulkSourceHeronRadialSquare
    timeBonds s hs stage leftTime
  let right := bulkSourceHeronRadialSquare
    timeBonds s hs stage rightTime
  let insertionPolynomials := insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
        timeBonds (bulkSourceWidth s) stage
        insertion.time insertion.face)
  change finiteGaussianThirdCumulant N
      (finiteGaussianCenteredPolynomial leftOldCenter left)
      (finiteGaussianCenteredPolynomial rightOldCenter right)
      (polySum insertionPolynomials) ≈
    openCubeBulkPlaquetteSpatialHeatActionFourthFamilyWickSum
      timeBonds s hs stage leftTime rightTime insertions
  have hcenter : finiteGaussianThirdCumulant N
        (finiteGaussianCenteredPolynomial leftOldCenter left)
        (finiteGaussianCenteredPolynomial rightOldCenter right)
        (polySum insertionPolynomials) ≈
      finiteGaussianThirdCumulant N left right
        (polySum insertionPolynomials) :=
    finiteGaussianThirdCumulant_center_left_middle N
      leftOldCenter rightOldCenter left right (polySum insertionPolynomials)
  have hsum : finiteGaussianThirdCumulant N left right
        (polySum insertionPolynomials) ≈
      qListSum (insertionPolynomials.map fun polynomial =>
        finiteGaussianThirdCumulant N left right polynomial) :=
    finiteGaussianThirdCumulant_polySum_right N left right
      insertionPolynomials
  have hterms : qListSum (insertionPolynomials.map fun polynomial =>
        finiteGaussianThirdCumulant N left right polynomial) ≈
      openCubeBulkPlaquetteSpatialHeatActionFourthFamilyWickSum
        timeBonds s hs stage leftTime rightTime insertions := by
    unfold insertionPolynomials
      openCubeBulkPlaquetteSpatialHeatActionFourthFamilyWickSum
    simp only [List.map_map]
    exact qListSum_congr _ _ insertions (fun insertion _ =>
      Q'.eqv_trans _ _ _
        (finiteGaussianThirdCumulant_smul_right N insertion.weight
          left right
          (combGaugeFreeHistoryPlaquetteSpatialHeatActionFourthPolynomial
            timeBonds (bulkSourceWidth s) stage
            insertion.time insertion.face))
        (Q'.mul_eqv_congr_left insertion.weight _ _
          (finiteGaussianThirdCumulant_openCube_bulk_spatialHeatActionFourth_wick
            timeBonds s hs stage leftTime rightTime
            insertion.time insertion.face)))
  exact Q'.eqv_trans _ _ _ hcenter (Q'.eqv_trans _ _ _ hsum hterms)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant.finiteGaussianThirdCumulant_weighted_row_squares_triangle
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant.finiteGaussianCayleyH2SquareActionPolynomial_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant.finiteGaussianCayleyH2ActionPolynomial_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant.finiteGaussianThirdCumulant_openCube_bulk_spatialHeatActionFourth_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialHeatActionCumulant.finiteGaussianThirdCumulant_openCube_bulk_old_centered_spatialHeatActionFourth_family_wick
