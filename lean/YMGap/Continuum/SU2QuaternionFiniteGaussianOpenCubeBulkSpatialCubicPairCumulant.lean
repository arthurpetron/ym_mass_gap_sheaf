/-
# Complete open-cube spatial cubic-pair cumulant

The complete second density coefficient contains `V3^2/2`, where `V3` is the
TOTAL spatial cubic action coefficient: the sum of `H3/4` over every internal
spatial face on every history slice.  The square is therefore a full ordered
double sum.  Cross-face and cross-time terms may not be replaced by a sum of
facewise squares.

This leaf instantiates the checked twenty-four-term Cayley cubic expansion on
the SAME directed rooted-comb/Heron plaquette rows, forms the complete ordered
half-square over `List.range (timeBonds+1)` and all internal spatial faces,
and reduces its connected insertion against two literal bulk-source
quadratics through the checked `2+2+6` row compiler.

The result is only an exact finite FREE reference-Gaussian identity.  It does
not prove a sign or cutoff- and volume-uniform bound, supply OWN/OLD mean
residuals, identify the ORIGINAL interacting/gauge-reduced law, control the
higher remainder, or establish a continuum Hamiltonian or physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoFourCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianTwoTwoSixCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianThirdCumulantTrilinear
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkNormalizedQuarticCumulant
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyCubicPairTerms

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_congr {A : Type} (f g : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → f item ≈ g item) →
    qListSum (items.map f) ≈ qListSum (items.map g)
  | [], _ => Q'.eqv_refl _
  | item :: items, h => Q'.add_eqv_congr' (h item List.mem_cons_self)
      (qListSum_congr f g items
        (fun other hother => h other (List.mem_cons_of_mem item hother)))

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

private theorem weightedTermPolynomial_flatMap {A : Type}
    (block : A → List (Q' × RatPoly)) : ∀ items : List A,
    RatPolyCoeffEqv
      (polySum (items.map fun item => weightedTermPolynomial (block item)))
      (weightedTermPolynomial (items.flatMap block))
  | [] => RatPolyCoeffEqv.refl _
  | item :: items =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (weightedTermPolynomial_flatMap block items))
        (weightedTermPolynomial_append
          (block item) (items.flatMap block))

/-- Explicit weighted sum of termwise `2+2+6` Wick reductions. -/
def finiteGaussianWeightedSexticRowBlocksWickSum
    (N : Nat)
    (left right : List WeightedQuadraticRowBlock)
    (insertions : List WeightedSexticRowBlock) : Q' :=
  qListSum (left.map fun leftTerm =>
    qListSum (right.map fun rightTerm =>
      qListSum (insertions.map fun insertionTerm =>
        leftTerm.weight * (rightTerm.weight *
          (insertionTerm.weight *
            finiteGaussianTwoTwoSixWickReduction N
              leftTerm.first leftTerm.second
              rightTerm.first rightTerm.second
              insertionTerm.first insertionTerm.second
              insertionTerm.third insertionTerm.fourth
              insertionTerm.fifth insertionTerm.sixth)))))

/-- Weighted finite sums of quadratic source blocks and sextic insertion
blocks reduce term-by-term to the checked `2+2+6` Wick expression. -/
theorem finiteGaussianThirdCumulant_weighted_sextic_row_blocks_wick
    (N : Nat)
    (left right : List WeightedQuadraticRowBlock)
    (insertions : List WeightedSexticRowBlock) :
    finiteGaussianThirdCumulant N
        (weightedTermPolynomial
          (left.map (weightedQuadraticRowBlockTerm N)))
        (weightedTermPolynomial
          (right.map (weightedQuadraticRowBlockTerm N)))
        (weightedTermPolynomial
          (insertions.map (weightedSexticRowBlockTerm N))) ≈
      finiteGaussianWeightedSexticRowBlocksWickSum
        N left right insertions := by
  have hsum := finiteGaussianThirdCumulant_weighted_polySum_three N
    (left.map (weightedQuadraticRowBlockTerm N))
    (right.map (weightedQuadraticRowBlockTerm N))
    (insertions.map (weightedSexticRowBlockTerm N))
  exact Q'.eqv_trans _ _ _ hsum (by
    simp only [List.map_map]
    exact qListSum_congr _ _ left (fun leftTerm _ =>
      qListSum_congr _ _ right (fun rightTerm _ =>
        qListSum_congr _ _ insertions (fun insertionTerm _ =>
          Q'.mul_eqv_congr_left leftTerm.weight _ _
            (Q'.mul_eqv_congr_left rightTerm.weight _ _
              (Q'.mul_eqv_congr_left insertionTerm.weight _ _
                (finiteGaussianThirdCumulant_row_blocks_six_wick N
                  leftTerm.first leftTerm.second
                  rightTerm.first rightTerm.second
                  insertionTerm.first insertionTerm.second
                  insertionTerm.third insertionTerm.fourth
                  insertionTerm.fifth insertionTerm.sixth)))))))

/-- The twenty-four exact `H3/4` row blocks on one actual directed
open-cube plaquette. -/
def openCubePlaquetteSpatialCubicRowBlocks
    (timeBonds width stage time : Nat) (face : Z4Plaq) :
    List WeightedCubicRowBlock :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianCayleySpatialCubicRowBlocks
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Literal `H3/4` polynomial on one actual directed open-cube plaquette. -/
def combGaugeFreeHistoryPlaquetteSpatialCubicPolynomial
    (timeBonds width stage time : Nat) (face : Z4Plaq) : RatPoly :=
  let rows := combGaugeFreeHistoryHeronDirectedPlaquetteRows
    timeBonds width stage time face
  finiteGaussianCayleySpatialCubicPolynomial
    (combGaugePlaquetteNoiseCount timeBonds width)
    (rows 0) (rows 1) (rows 2) (rows 3)

/-- Canonical complete spatial-cubic insertion sites: every history slice and
every internal spatial face. -/
def completeOpenCubeSpatialCubicSites
    (timeBonds width : Nat) : List (Nat × Z4Plaq) :=
  (List.range (timeBonds + 1)).flatMap fun time =>
    (internalOpenCubeFaces width).map fun face => (time, face)

/-- All exact cubic row blocks of the TOTAL finite spatial `V3`. -/
def completeOpenCubeSpatialCubicRowBlocks
    (timeBonds width stage : Nat) : List WeightedCubicRowBlock :=
  (completeOpenCubeSpatialCubicSites timeBonds width).flatMap fun site =>
    openCubePlaquetteSpatialCubicRowBlocks
      timeBonds width stage site.1 site.2

/-- Literal TOTAL spatial cubic polynomial, summed over every history slice
and every internal spatial face. -/
def completeOpenCubeSpatialCubicPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  polySum ((completeOpenCubeSpatialCubicSites timeBonds width).map fun site =>
    combGaugeFreeHistoryPlaquetteSpatialCubicPolynomial
      timeBonds width stage site.1 site.2)

/-- The literal complete face/time sum equals its flattened list of exact
twenty-four-term cubic row blocks. -/
theorem completeOpenCubeSpatialCubicPolynomial_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeSpatialCubicPolynomial timeBonds width stage)
      (weightedTermPolynomial
        ((completeOpenCubeSpatialCubicRowBlocks
          timeBonds width stage).map
            (weightedCubicRowBlockTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  let N := combGaugePlaquetteNoiseCount timeBonds width
  let sites := completeOpenCubeSpatialCubicSites timeBonds width
  let blocks := fun site : Nat × Z4Plaq =>
    openCubePlaquetteSpatialCubicRowBlocks
      timeBonds width stage site.1 site.2
  have hflat := weightedTermPolynomial_flatMap
    (fun site => (blocks site).map (weightedCubicRowBlockTerm N)) sites
  unfold completeOpenCubeSpatialCubicPolynomial
    combGaugeFreeHistoryPlaquetteSpatialCubicPolynomial
    finiteGaussianCayleySpatialCubicPolynomial
    completeOpenCubeSpatialCubicRowBlocks
    openCubePlaquetteSpatialCubicRowBlocks
  change RatPolyCoeffEqv
    (polySum (sites.map fun site =>
      weightedTermPolynomial
        ((blocks site).map (weightedCubicRowBlockTerm N))))
    (weightedTermPolynomial
      ((sites.flatMap blocks).map (weightedCubicRowBlockTerm N)))
  simpa only [List.map_flatMap] using hflat

/-- Literal complete ordered half-square `V3^2/2`. -/
def completeOpenCubeSpatialCubicPairPolynomial
    (timeBonds width stage : Nat) : RatPoly :=
  let cubic := completeOpenCubeSpatialCubicPolynomial
    timeBonds width stage
  polySmul cubicPairHalf (polyMul cubic cubic)

/-- Complete explicit sextic row blocks of `V3^2/2`.  The Cartesian product
is ordered and therefore retains every cross-face and cross-time term. -/
def completeOpenCubeSpatialCubicPairSexticRowBlocks
    (timeBonds width stage : Nat) : List WeightedSexticRowBlock :=
  let cubicBlocks := completeOpenCubeSpatialCubicRowBlocks
    timeBonds width stage
  finiteGaussianCubicPairSexticRowBlocks cubicBlocks cubicBlocks

/-- The literal total half-square is exactly the complete ordered sextic row
list, coefficient by coefficient. -/
theorem completeOpenCubeSpatialCubicPairPolynomial_coeffEqv
    (timeBonds width stage : Nat) :
    RatPolyCoeffEqv
      (completeOpenCubeSpatialCubicPairPolynomial
        timeBonds width stage)
      (weightedTermPolynomial
        ((completeOpenCubeSpatialCubicPairSexticRowBlocks
          timeBonds width stage).map
            (weightedSexticRowBlockTerm
              (combGaugePlaquetteNoiseCount timeBonds width)))) := by
  let N := combGaugePlaquetteNoiseCount timeBonds width
  let cubic := completeOpenCubeSpatialCubicPolynomial
    timeBonds width stage
  let cubicBlocks := completeOpenCubeSpatialCubicRowBlocks
    timeBonds width stage
  have hcubic := completeOpenCubeSpatialCubicPolynomial_coeffEqv
    timeBonds width stage
  have hsquare := (hcubic.mul hcubic).smul cubicPairHalf
  have hpairs := finiteGaussianCubicPairPolynomial_coeffEqv
    N cubicBlocks cubicBlocks
  unfold completeOpenCubeSpatialCubicPairPolynomial
    completeOpenCubeSpatialCubicPairSexticRowBlocks
  exact RatPolyCoeffEqv.trans hsquare hpairs

/-- Exact finite Wick sum for the two actual bulk sources and the complete
TOTAL spatial cubic half-square insertion. -/
def openCubeBulkCompleteSpatialCubicPairWickSum
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat) : Q' :=
  finiteGaussianWeightedSexticRowBlocksWickSum
    (bulkSourceNoiseCount timeBonds s)
    (bulkSourceHeronQuadraticRowBlocks timeBonds s hs stage leftTime)
    (bulkSourceHeronQuadraticRowBlocks timeBonds s hs stage rightTime)
    (completeOpenCubeSpatialCubicPairSexticRowBlocks
      timeBonds (bulkSourceWidth s) stage)

/-- The connected insertion of the complete finite `V3^2/2` against two
literal open-cube bulk-source quadratics is exactly the displayed weighted
sum of checked `2+2+6` Wick reductions. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_completeSpatialCubicPair_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat) :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
        (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
        (completeOpenCubeSpatialCubicPairPolynomial
          timeBonds (bulkSourceWidth s) stage) ≈
      openCubeBulkCompleteSpatialCubicPairWickSum
        timeBonds s hs stage leftTime rightTime := by
  let N := bulkSourceNoiseCount timeBonds s
  let leftBlocks := bulkSourceHeronQuadraticRowBlocks
    timeBonds s hs stage leftTime
  let rightBlocks := bulkSourceHeronQuadraticRowBlocks
    timeBonds s hs stage rightTime
  let insertionBlocks := completeOpenCubeSpatialCubicPairSexticRowBlocks
    timeBonds (bulkSourceWidth s) stage
  have hnoise : combGaugePlaquetteNoiseCount
      timeBonds (bulkSourceWidth s) = N := by
    unfold combGaugePlaquetteNoiseCount N bulkSourceNoiseCount
    rfl
  have hinsertion := completeOpenCubeSpatialCubicPairPolynomial_coeffEqv
    timeBonds (bulkSourceWidth s) stage
  rw [hnoise] at hinsertion
  rw [bulkSourceHeronRadialSquare_eq_quadraticTerms,
    bulkSourceHeronRadialSquare_eq_quadraticTerms,
    bulkSourceHeronQuadraticTerms_eq_rowBlocks,
    bulkSourceHeronQuadraticTerms_eq_rowBlocks]
  change finiteGaussianThirdCumulant N
      (weightedTermPolynomial
        (leftBlocks.map (weightedQuadraticRowBlockTerm N)))
      (weightedTermPolynomial
        (rightBlocks.map (weightedQuadraticRowBlockTerm N)))
      (completeOpenCubeSpatialCubicPairPolynomial
        timeBonds (bulkSourceWidth s) stage) ≈
    finiteGaussianWeightedSexticRowBlocksWickSum
      N leftBlocks rightBlocks insertionBlocks
  exact Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_coeffEqv N
      (RatPolyCoeffEqv.refl _) (RatPolyCoeffEqv.refl _) hinsertion)
    (finiteGaussianThirdCumulant_weighted_sextic_row_blocks_wick
      N leftBlocks rightBlocks insertionBlocks)

/-- Arbitrary scalar OLD centers cancel inside the connected complete
`V3^2/2` insertion.  The separate OWN/OLD mean-residual products remain
outside this identity. -/
theorem finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeSpatialCubicPair_wick
    (timeBonds s : Nat) (hs : 0 < s)
    (stage leftTime rightTime : Nat)
    (leftOldCenter rightOldCenter : Q') :
    finiteGaussianThirdCumulant (bulkSourceNoiseCount timeBonds s)
        (finiteGaussianCenteredPolynomial leftOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime))
        (finiteGaussianCenteredPolynomial rightOldCenter
          (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime))
        (completeOpenCubeSpatialCubicPairPolynomial
          timeBonds (bulkSourceWidth s) stage) ≈
      openCubeBulkCompleteSpatialCubicPairWickSum
        timeBonds s hs stage leftTime rightTime :=
  Q'.eqv_trans _ _ _
    (finiteGaussianThirdCumulant_center_left_middle
      (bulkSourceNoiseCount timeBonds s) leftOldCenter rightOldCenter
      (bulkSourceHeronRadialSquare timeBonds s hs stage leftTime)
      (bulkSourceHeronRadialSquare timeBonds s hs stage rightTime)
      (completeOpenCubeSpatialCubicPairPolynomial
        timeBonds (bulkSourceWidth s) stage))
    (finiteGaussianThirdCumulant_openCube_bulk_completeSpatialCubicPair_wick
      timeBonds s hs stage leftTime rightTime)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant.finiteGaussianThirdCumulant_weighted_sextic_row_blocks_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant.completeOpenCubeSpatialCubicPolynomial_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant.completeOpenCubeSpatialCubicPairPolynomial_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant.finiteGaussianThirdCumulant_openCube_bulk_completeSpatialCubicPair_wick
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSpatialCubicPairCumulant.finiteGaussianThirdCumulant_openCube_bulk_old_centered_completeSpatialCubicPair_wick
