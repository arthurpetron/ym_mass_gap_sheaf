/-
# Actual open-cube bulk-source/normalized-quartic Gaussian cumulant

This leaf joins the exact finite term lists already attached to the open-cube
bulk source and to one actual plaquette's normalized Cayley quartic.  It first
records the underlying weighted two-row and four-row blocks, then applies the
checked trilinearity theorem and the checked `2+2+4` Wick reduction to every
term of the resulting finite triple sum.

The output is an exact finite reference-Gaussian identity.  It does not prove
a sign, a cutoff-uniform estimate, an OLD-center coefficient, an interacting
ORIGINAL-law comparison, a higher-remainder bound, or a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
import YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuarticDotIdentity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows

local infix:50 " ≈ " => Q'.eqv

/-- A rationally weighted ordered quadratic row word. -/
structure WeightedQuadraticRowBlock where
  weight : Q'
  first : Nat → Q'
  second : Nat → Q'

/-- A rationally weighted ordered quartic row word. -/
structure WeightedQuarticRowBlock where
  weight : Q'
  first : Nat → Q'
  second : Nat → Q'
  third : Nat → Q'
  fourth : Nat → Q'

def weightedQuadraticRowBlockTerm (N : Nat)
    (term : WeightedQuadraticRowBlock) : Q' × RatPoly :=
  (term.weight, finiteGaussianRowWord N [term.first, term.second])

def weightedQuarticRowBlockTerm (N : Nat)
    (term : WeightedQuarticRowBlock) : Q' × RatPoly :=
  (term.weight,
    finiteGaussianRowWord N
      [term.first, term.second, term.third, term.fourth])

/-- The explicit weighted sum of termwise `2+2+4` Wick reductions. -/
def finiteGaussianWeightedRowBlocksWickSum
    (N : Nat)
    (left right : List WeightedQuadraticRowBlock)
    (insertions : List WeightedQuarticRowBlock) : Q' :=
  qListSum (left.map fun leftTerm =>
    qListSum (right.map fun rightTerm =>
      qListSum (insertions.map fun insertionTerm =>
        leftTerm.weight * (rightTerm.weight *
          (insertionTerm.weight *
            finiteGaussianTwoTwoFourWickReduction N
              leftTerm.first leftTerm.second
              rightTerm.first rightTerm.second
              insertionTerm.first insertionTerm.second
              insertionTerm.third insertionTerm.fourth)))))

private theorem qListSum_congr {A : Type} (f g : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → f item ≈ g item) →
    qListSum (items.map f) ≈ qListSum (items.map g)
  | [], _ => Q'.eqv_refl _
  | item :: items, h => Q'.add_eqv_congr' (h item List.mem_cons_self)
      (qListSum_congr f g items
        (fun other hother => h other (List.mem_cons_of_mem item hother)))

/-- Weighted finite sums of explicit row blocks reduce term-by-term to the
checked `2+2+4` Wick expression. -/
theorem finiteGaussianThirdCumulant_weighted_row_blocks_wick
    (N : Nat)
    (left right : List WeightedQuadraticRowBlock)
    (insertions : List WeightedQuarticRowBlock) :
    finiteGaussianThirdCumulant N
        (weightedTermPolynomial
          (left.map (weightedQuadraticRowBlockTerm N)))
        (weightedTermPolynomial
          (right.map (weightedQuadraticRowBlockTerm N)))
        (weightedTermPolynomial
          (insertions.map (weightedQuarticRowBlockTerm N))) ≈
      finiteGaussianWeightedRowBlocksWickSum N left right insertions := by
  have hsum := finiteGaussianThirdCumulant_weighted_polySum_three N
    (left.map (weightedQuadraticRowBlockTerm N))
    (right.map (weightedQuadraticRowBlockTerm N))
    (insertions.map (weightedQuarticRowBlockTerm N))
  exact Q'.eqv_trans _ _ _ hsum (by
    simp only [List.map_map]
    exact qListSum_congr _ _ left (fun leftTerm _ =>
      qListSum_congr _ _ right (fun rightTerm _ =>
        qListSum_congr _ _ insertions (fun insertionTerm _ =>
          Q'.mul_eqv_congr_left leftTerm.weight _ _
            (Q'.mul_eqv_congr_left rightTerm.weight _ _
              (Q'.mul_eqv_congr_left insertionTerm.weight _ _
                (finiteGaussianThirdCumulant_row_blocks_wick N
                  leftTerm.first leftTerm.second
                  rightTerm.first rightTerm.second
                  insertionTerm.first insertionTerm.second
                  insertionTerm.third insertionTerm.fourth)))))))

/-- Weighted two-row blocks of one literal open-cube bulk source. -/
def bulkSourceHeronQuadraticRowBlocks
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) :
    List WeightedQuadraticRowBlock :=
  (List.range (3 * (bulkSourceFaces s).length)).map fun rowIndex =>
    let row := bulkSourceHeronColorCurlRow timeBonds s stage time rowIndex
    { weight := bulkSourceIndexWeight s hs (rowIndex / 3)
      first := row
      second := row }

theorem bulkSourceHeronQuadraticTerms_eq_rowBlocks
    (timeBonds s : Nat) (hs : 0 < s) (stage time : Nat) :
    bulkSourceHeronQuadraticTerms timeBonds s hs stage time =
      (bulkSourceHeronQuadraticRowBlocks
        timeBonds s hs stage time).map
          (weightedQuadraticRowBlockTerm
            (bulkSourceNoiseCount timeBonds s)) := by
  unfold bulkSourceHeronQuadraticTerms bulkSourceHeronQuadraticRowBlocks
    weightedQuadraticRowBlockTerm finiteGaussianRowSquare
    finiteGaussianRowWord
  simp only [List.map_map]
  rfl

/-- Four-row blocks supplied by one signed term of the shared exact `H4`. -/
def finiteGaussianH4TermQuarticRowBlocks
    (slots : Nat → Nat → Nat → Q') (term : H4DotTerm) :
    List WeightedQuarticRowBlock :=
  (List.range 3).flatMap fun leftComponent =>
    (List.range 3).map fun rightComponent =>
      { weight := Q'.ofInt term.weight
        first := slots term.firstLeft leftComponent
        second := slots term.firstRight leftComponent
        third := slots term.secondLeft rightComponent
        fourth := slots term.secondRight rightComponent }

/-- Four-row blocks supplied by the normalized Cayley denominator correction. -/
def finiteGaussianCayleyDenominatorQuarticRowBlocks
    (slots : Nat → Nat → Nat → Q') : List WeightedQuarticRowBlock :=
  let normRows := gaussianCayleyNormRows slots
  let totalRows := gaussianCayleyTotalRows slots
  (List.range 12).flatMap fun normComponent =>
    (List.range 3).map fun totalComponent =>
      { weight := Q'.ofInt (-4)
        first := normRows normComponent
        second := normRows normComponent
        third := totalRows totalComponent
        fourth := totalRows totalComponent }

/-- Complete four-row block list of the normalized Cayley quartic. -/
def finiteGaussianNormalizedCayleyH4QuarticRowBlocks
    (a b c d : Nat → Nat → Q') : List WeightedQuarticRowBlock :=
  let slots := gaussianCayleySlot a b c d
  h4DotTerms.flatMap (finiteGaussianH4TermQuarticRowBlocks slots) ++
    finiteGaussianCayleyDenominatorQuarticRowBlocks slots

theorem finiteGaussianNormalizedCayleyH4QuarticTerms_eq_rowBlocks
    (N : Nat) (a b c d : Nat → Nat → Q') :
    finiteGaussianNormalizedCayleyH4QuarticTerms N a b c d =
      (finiteGaussianNormalizedCayleyH4QuarticRowBlocks a b c d).map
        (weightedQuarticRowBlockTerm N) := by
  unfold finiteGaussianNormalizedCayleyH4QuarticTerms
    finiteGaussianCayleyH4QuarticTerms
    finiteGaussianH4TermQuarticTerms
    finiteGaussianCayleyDenominatorQuarticTerms
    finiteGaussianNormalizedCayleyH4QuarticRowBlocks
    finiteGaussianH4TermQuarticRowBlocks
    finiteGaussianCayleyDenominatorQuarticRowBlocks
    weightedQuarticRowBlockTerm
  simp only [List.map_append, List.map_flatMap, List.map_map]
  rfl

/-- Actual normalized-quartic row blocks of one rooted-comb-gauge open-cube
plaquette. -/
def openCubePlaquetteNormalizedH4RowBlocks
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedQuarticRowBlock :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianNormalizedCayleyH4QuarticRowBlocks
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Exact finite Wick sum for two actual bulk-source times and one actual
normalized-quartic plaquette insertion. -/
def openCubeBulkPlaquetteNormalizedH4WickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq) : Q' :=
  finiteGaussianWeightedRowBlocksWickSum
    (bulkSourceNoiseCount timeBonds s)
    (bulkSourceHeronQuadraticRowBlocks timeBonds s hs stage leftTime)
    (bulkSourceHeronQuadraticRowBlocks timeBonds s hs stage rightTime)
    (openCubePlaquetteNormalizedH4RowBlocks
      timeBonds (bulkSourceWidth s) stage insertionTime face)

/-- The third cumulant of two literal bulk-source observables and one literal
normalized Cayley quartic on an actual finite open-cube plaquette is exactly
the displayed finite weighted sum of checked `2+2+4` Wick reductions. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_normalizedH4_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (bulkSourceHeronRadialSquare
          timeBonds s hs stage leftTime)
        (bulkSourceHeronRadialSquare
          timeBonds s hs stage rightTime)
        (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
          timeBonds (bulkSourceWidth s) stage insertionTime face) ≈
      openCubeBulkPlaquetteNormalizedH4WickSum
        timeBonds s hs stage leftTime rightTime insertionTime face := by
  let N := bulkSourceNoiseCount timeBonds s
  let leftBlocks := bulkSourceHeronQuadraticRowBlocks
    timeBonds s hs stage leftTime
  let rightBlocks := bulkSourceHeronQuadraticRowBlocks
    timeBonds s hs stage rightTime
  let insertionBlocks := openCubePlaquetteNormalizedH4RowBlocks
    timeBonds (bulkSourceWidth s) stage insertionTime face
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds (bulkSourceWidth s) stage insertionTime face
  have hnoise : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth s) = N := by
    unfold combGaugePlaquetteNoiseCount N bulkSourceNoiseCount
    rfl
  have hinsertion :=
    finiteGaussianNormalizedCayleyH4Polynomial_quarticTerms
      N (rows 0) (rows 1) (rows 2) (rows 3)
  rw [finiteGaussianNormalizedCayleyH4QuarticTerms_eq_rowBlocks]
    at hinsertion
  have hactualInsertion : RatPolyCoeffEqv
      (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
        timeBonds (bulkSourceWidth s) stage insertionTime face)
      (weightedTermPolynomial
        (insertionBlocks.map (weightedQuarticRowBlockTerm N))) := by
    unfold combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
    rw [hnoise]
    exact hinsertion
  rw [bulkSourceHeronRadialSquare_eq_quadraticTerms,
    bulkSourceHeronRadialSquare_eq_quadraticTerms,
    bulkSourceHeronQuadraticTerms_eq_rowBlocks,
    bulkSourceHeronQuadraticTerms_eq_rowBlocks]
  change finiteGaussianThirdCumulant N
      (weightedTermPolynomial
        (leftBlocks.map (weightedQuadraticRowBlockTerm N)))
      (weightedTermPolynomial
        (rightBlocks.map (weightedQuadraticRowBlockTerm N)))
      (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
        timeBonds (bulkSourceWidth s) stage insertionTime face) ≈
    finiteGaussianWeightedRowBlocksWickSum
      N leftBlocks rightBlocks insertionBlocks
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_coeffEqv N
      (RatPolyCoeffEqv.refl _) (RatPolyCoeffEqv.refl _) hactualInsertion)
    (finiteGaussianThirdCumulant_weighted_row_blocks_wick
      N leftBlocks rightBlocks insertionBlocks)

/-- Arbitrary scalar OLD centers cancel from this connected quartic insertion.
The separate mean-residual products in the complete OLD-centered order-six
response are not part of this cumulant identity. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_normalizedH4_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime insertionTime : Nat) (face : Z4Plaq)
    (leftOldCenter rightOldCenter : Q') :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare
            timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare
            timeBonds s hs stage rightTime))
        (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
          timeBonds (bulkSourceWidth s) stage insertionTime face) ≈
      openCubeBulkPlaquetteNormalizedH4WickSum
        timeBonds s hs stage leftTime rightTime insertionTime face :=
  Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_center_left_middle
      (bulkSourceNoiseCount timeBonds s) leftOldCenter rightOldCenter
      (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
      (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
      (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
        timeBonds (bulkSourceWidth s) stage insertionTime face))
    (finiteGaussianThirdCumulant_openCube_bulk_normalizedH4_wick
      timeBonds s hs stage leftTime rightTime insertionTime face)

/-- One weighted normalized-quartic plaquette insertion at a specified
history time. -/
structure OpenCubeNormalizedH4Insertion where
  weight : Q'
  time : Nat
  face : Z4Plaq

/-- Literal polynomial sum of a finite weighted plaquette-insertion family. -/
def openCubeNormalizedH4InsertionPolynomial
    (timeBonds width stage : Nat)
    (insertions : List OpenCubeNormalizedH4Insertion) : RatPoly :=
  polySum (insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
        timeBonds width stage insertion.time insertion.face))

/-- Corresponding finite weighted sum of the exact one-plaquette Wick sums. -/
def openCubeBulkPlaquetteNormalizedH4FamilyWickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (insertions : List OpenCubeNormalizedH4Insertion) : Q' :=
  qListSum (insertions.map fun insertion =>
    insertion.weight *
      openCubeBulkPlaquetteNormalizedH4WickSum
        timeBonds s hs stage leftTime rightTime
        insertion.time insertion.face)

/-- The literal OLD-centered finite Gaussian response to a weighted
normalized-quartic insertion family. -/
def openCubeBulkOldCenteredNormalizedH4FamilyCumulant
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q')
    (insertions : List OpenCubeNormalizedH4Insertion) : Q' :=
  finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
    (finiteGaussianCenteredPolynomial leftOldCenter
      (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
    (finiteGaussianCenteredPolynomial rightOldCenter
      (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
    (openCubeNormalizedH4InsertionPolynomial
      timeBonds (bulkSourceWidth s) stage insertions)

/-- Exact family consumer: arbitrary scalar OLD centers and an arbitrary
finite weighted list of actual plaquette/time normalized-quartic insertions
reduce to the corresponding finite sum of checked Wick expressions. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_normalizedH4_family_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q')
    (insertions : List OpenCubeNormalizedH4Insertion) :
    openCubeBulkOldCenteredNormalizedH4FamilyCumulant
        timeBonds s hs stage leftTime rightTime
        leftOldCenter rightOldCenter insertions ≈
      openCubeBulkPlaquetteNormalizedH4FamilyWickSum
        timeBonds s hs stage leftTime rightTime insertions := by
  let N := bulkSourceNoiseCount timeBonds s
  let left := bulkSourceHeronRadialSquare
    timeBonds s hs stage leftTime
  let right := bulkSourceHeronRadialSquare
    timeBonds s hs stage rightTime
  let insertionPolynomials := insertions.map fun insertion =>
    polySmul insertion.weight
      (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
        timeBonds (bulkSourceWidth s) stage
        insertion.time insertion.face)
  change finiteGaussianThirdCumulant N
      (finiteGaussianCenteredPolynomial leftOldCenter left)
      (finiteGaussianCenteredPolynomial rightOldCenter right)
      (polySum insertionPolynomials) ≈
    openCubeBulkPlaquetteNormalizedH4FamilyWickSum
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
      openCubeBulkPlaquetteNormalizedH4FamilyWickSum
        timeBonds s hs stage leftTime rightTime insertions := by
    unfold insertionPolynomials
      openCubeBulkPlaquetteNormalizedH4FamilyWickSum
    simp only [List.map_map]
    exact qListSum_congr _ _ insertions (fun insertion _ =>
      Q'.eqv_trans _ _ _
        (finiteGaussianThirdCumulant_smul_right N insertion.weight
          left right
          (combGaugeFreeHistoryPlaquetteNormalizedH4Polynomial
            timeBonds (bulkSourceWidth s) stage
            insertion.time insertion.face))
        (Q'.mul_eqv_congr_left insertion.weight _ _
          (finiteGaussianThirdCumulant_openCube_bulk_normalizedH4_wick
            timeBonds s hs stage leftTime rightTime
            insertion.time insertion.face)))
  exact Q'.eqv_trans _ _ _ hcenter (Q'.eqv_trans _ _ _ hsum hterms)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant.finiteGaussianThirdCumulant_weighted_row_blocks_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant.finiteGaussianThirdCumulant_openCube_bulk_normalizedH4_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant.finiteGaussianThirdCumulant_openCube_bulk_old_centered_normalizedH4_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant.finiteGaussianThirdCumulant_openCube_bulk_old_centered_normalizedH4_family_wick
