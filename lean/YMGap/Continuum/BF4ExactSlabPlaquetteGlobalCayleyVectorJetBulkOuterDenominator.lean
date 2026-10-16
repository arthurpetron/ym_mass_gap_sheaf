/-
# Parametric outer-denominator split of the centered Cayley vector jet

The weighted quadratic source from the exact cleared vector-jet identity is
`4*D*P2`.  For an arbitrary rational reference scale `c`, this file separates
it exactly into `4*c*P2` and `4*(D-c)*P2`, aggregates both pieces over the
literal chronological bulk source, and performs the corresponding centered
ORIGINAL expectation split.

The reference scale is deliberately not pinned here.  The inner denominator
powers already present in `P2` also remain explicit.  No deformation bound,
FREE Gaussian identification, cutoff removal, continuum theory, or mass gap
is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetPair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.QuaternionHaarGammaFiniteSum
  (finitePolySum_add)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev PE := PolyExpr
local infix:50 " ≈ " => Q'.eqv

/-- The outer Cayley denominator frozen at an arbitrary rational reference
scale, while the complete inner degree-two polynomial remains unchanged. -/
def globalCayleyVectorJetReferenceQuadraticPolynomial
    (reference : Q') (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polyMul (polyConst 4) (polyConst reference))
    (globalCayleyDegreeTwoPolynomial extent face)

/-- Exact deformation contributed by replacing the outer Cayley denominator
with the supplied reference scale. -/
def globalCayleyVectorJetOuterDenominatorRemainderPolynomial
    (reference : Q') (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polyMul (polyConst 4)
      (polyAdd
        (globalCayleyDenominatorPolynomial extent face)
        (polyNeg (polyConst reference))))
    (globalCayleyDegreeTwoPolynomial extent face)

private theorem outerDenominator_split_coeff
    (reference : Q') (denominator quadratic : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul (polyConst 4) denominator) quadratic)
      (polyAdd
        (polyMul (polyMul (polyConst 4) (polyConst reference)) quadratic)
        (polyMul
          (polyMul (polyConst 4)
            (polyAdd denominator (polyNeg (polyConst reference))))
          quadratic)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.const 4) (.var 0)) (.var 1))
    (.add
      (.mul (.mul (.const 4) (.var 2)) (.var 1))
      (.mul
        (.mul (.const 4) (.add (.var 0) (.neg (.var 2))))
        (.var 1)))
    (by decide)
    (fun
      | 0 => denominator
      | 1 => quadratic
      | _ => polyConst reference)

/-- Exact coefficientwise split of the one-face extracted quadratic carrier
at an arbitrary outer-denominator reference scale. -/
theorem globalCayleyVectorJetQuadratic_outerDenominator_split
    (reference : Q') (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleyVectorJetQuadraticPolynomial extent face)
      (polyAdd
        (globalCayleyVectorJetReferenceQuadraticPolynomial
          reference extent face)
        (globalCayleyVectorJetOuterDenominatorRemainderPolynomial
          reference extent face)) := by
  simpa [globalCayleyVectorJetQuadraticPolynomial,
    globalCayleyVectorJetReferenceQuadraticPolynomial,
    globalCayleyVectorJetOuterDenominatorRemainderPolynomial] using
      outerDenominator_split_coeff reference
        (globalCayleyDenominatorPolynomial extent face)
        (globalCayleyDegreeTwoPolynomial extent face)

/-- Literal weighted reference-scale quadratic source at one chronological
placement. -/
def globalCayleyVectorJetBulkReferenceQuadraticSource
    (reference : Q') (s : Nat) (hs : 0 < s)
    (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetReferenceQuadraticPolynomial
        reference extent (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

/-- Literal weighted outer-denominator deformation source. -/
def globalCayleyVectorJetBulkOuterDenominatorRemainderSource
    (reference : Q') (s : Nat) (hs : 0 < s)
    (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetOuterDenominatorRemainderPolynomial
        reference extent (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

private theorem finiteSum_coeff
    {Index : Type} (left right : Index → RatPoly) :
    ∀ items : List Index,
      (∀ index, index ∈ items → RatPolyCoeffEqv (left index) (right index)) →
      RatPolyCoeffEqv (finitePolySum left items) (finitePolySum right items)
  | [], _ => RatPolyCoeffEqv.refl polyZero
  | index :: items, h =>
      RatPolyCoeffEqv.add (h index List.mem_cons_self)
        (finiteSum_coeff left right items
          (fun next hnext => h next (List.mem_cons_of_mem index hnext)))

/-- The complete weighted quadratic source splits coefficientwise into its
reference-scale part and exact outer-denominator deformation. -/
theorem globalCayleyVectorJetBulkQuadratic_outerDenominator_split
    (reference : Q') (s : Nat) (hs : 0 < s)
    (extent time : Nat) :
    RatPolyCoeffEqv
      (globalCayleyVectorJetBulkQuadraticSource s hs extent time)
      (polyAdd
        (globalCayleyVectorJetBulkReferenceQuadraticSource
          reference s hs extent time)
        (globalCayleyVectorJetBulkOuterDenominatorRemainderSource
          reference s hs extent time)) := by
  let quadratic := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetQuadraticPolynomial extent
        (timeShiftPlaquette time face))
  let referenceTerm := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetReferenceQuadraticPolynomial
        reference extent (timeShiftPlaquette time face))
  let remainderTerm := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetOuterDenominatorRemainderPolynomial
        reference extent (timeShiftPlaquette time face))
  have hsum := finiteSum_coeff quadratic
    (fun face => polyAdd (referenceTerm face) (remainderTerm face))
    (bulkSourceFaces s) (fun face _ => by
      have hface :=
        (globalCayleyVectorJetQuadratic_outerDenominator_split
          reference extent (timeShiftPlaquette time face)).smul
            (bulkSourceCoefficient s hs face)
      exact hface.trans
        (RatPolyCoeffEqv.smul_add (bulkSourceCoefficient s hs face)
          (globalCayleyVectorJetReferenceQuadraticPolynomial
            reference extent (timeShiftPlaquette time face))
          (globalCayleyVectorJetOuterDenominatorRemainderPolynomial
            reference extent (timeShiftPlaquette time face))))
  have hseparate := finitePolySum_add
    referenceTerm remainderTerm (bulkSourceFaces s)
  change RatPolyCoeffEqv
    (finitePolySum quadratic (bulkSourceFaces s))
    (polyAdd
      (finitePolySum referenceTerm (bulkSourceFaces s))
      (finitePolySum remainderTerm (bulkSourceFaces s)))
  exact hsum.trans hseparate

/-- Product of the two literal weighted reference-scale sources. -/
def globalCayleyVectorJetBulkPairReferenceQuadraticSource
    (reference : Q') (s : Nat) (hs : 0 < s)
    (extent leftTime rightTime : Nat) : RatPoly :=
  polyMul
    (globalCayleyVectorJetBulkReferenceQuadraticSource
      reference s hs extent leftTime)
    (globalCayleyVectorJetBulkReferenceQuadraticSource
      reference s hs extent rightTime)

/-- The three aggregate products containing at least one outer-denominator
deformation source. -/
def globalCayleyVectorJetBulkPairOuterDenominatorRemainderSource
    (reference : Q') (s : Nat) (hs : 0 < s)
    (extent leftTime rightTime : Nat) : RatPoly :=
  let leftReference := globalCayleyVectorJetBulkReferenceQuadraticSource
    reference s hs extent leftTime
  let rightReference := globalCayleyVectorJetBulkReferenceQuadraticSource
    reference s hs extent rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkOuterDenominatorRemainderSource
      reference s hs extent leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkOuterDenominatorRemainderSource
      reference s hs extent rightTime
  polyAdd
    (polyMul leftReference rightRemainder)
    (polyAdd
      (polyMul leftRemainder rightReference)
      (polyMul leftRemainder rightRemainder))

/-- Exact pair split of the complete weighted quadratic sources at an
arbitrary outer-denominator reference scale. -/
theorem globalCayleyVectorJetBulkPairQuadratic_outerDenominator_split
    (reference : Q') (s : Nat) (hs : 0 < s)
    (extent leftTime rightTime : Nat) :
    RatPolyCoeffEqv
      (polyMul
        (globalCayleyVectorJetBulkQuadraticSource s hs extent leftTime)
        (globalCayleyVectorJetBulkQuadraticSource s hs extent rightTime))
      (polyAdd
        (globalCayleyVectorJetBulkPairReferenceQuadraticSource
          reference s hs extent leftTime rightTime)
        (globalCayleyVectorJetBulkPairOuterDenominatorRemainderSource
          reference s hs extent leftTime rightTime)) := by
  let leftReference := globalCayleyVectorJetBulkReferenceQuadraticSource
    reference s hs extent leftTime
  let rightReference := globalCayleyVectorJetBulkReferenceQuadraticSource
    reference s hs extent rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkOuterDenominatorRemainderSource
      reference s hs extent leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkOuterDenominatorRemainderSource
      reference s hs extent rightTime
  have hleft := globalCayleyVectorJetBulkQuadratic_outerDenominator_split
    reference s hs extent leftTime
  change RatPolyCoeffEqv
    (globalCayleyVectorJetBulkQuadraticSource s hs extent leftTime)
    (polyAdd leftReference leftRemainder) at hleft
  have hright := globalCayleyVectorJetBulkQuadratic_outerDenominator_split
    reference s hs extent rightTime
  change RatPolyCoeffEqv
    (globalCayleyVectorJetBulkQuadraticSource s hs extent rightTime)
    (polyAdd rightReference rightRemainder) at hright
  have hproduct := RatPolyCoeffEqv.mul hleft hright
  have hdistribute : RatPolyCoeffEqv
      (polyMul (polyAdd leftReference leftRemainder)
        (polyAdd rightReference rightRemainder))
      (polyAdd
        (polyAdd
          (polyMul leftReference rightReference)
          (polyMul leftReference rightRemainder))
        (polyAdd
          (polyMul leftRemainder rightReference)
          (polyMul leftRemainder rightRemainder))) := by
    rw [polyMul_add_left_exact]
    exact RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.mul_add_right
        leftReference rightReference rightRemainder)
      (RatPolyCoeffEqv.mul_add_right
        leftRemainder rightReference rightRemainder)
  exact hproduct.trans (hdistribute.trans
    (RatPolyCoeffEqv.add_assoc
      (polyMul leftReference rightReference)
      (polyMul leftReference rightRemainder)
      (polyAdd
        (polyMul leftRemainder rightReference)
        (polyMul leftRemainder rightRemainder))))

/-- Normalized ORIGINAL expectation of one weighted reference-scale source. -/
def globalCayleyVectorJetBulkReferenceQuadraticExpectation
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkReferenceQuadraticSource
      reference s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of one weighted outer-denominator
deformation source. -/
def globalCayleyVectorJetBulkOuterDenominatorRemainderExpectation
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkOuterDenominatorRemainderSource
      reference s hs (centralExtent half) time)

/-- The one-source outer-denominator split passes exactly to the normalized
ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkQuadraticExpectation_outerDenominator_split
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkQuadraticExpectation
        w hw0 hw1 half s hs time)
      (CReal.add
        (globalCayleyVectorJetBulkReferenceQuadraticExpectation
          reference w hw0 hw1 half s hs time)
        (globalCayleyVectorJetBulkOuterDenominatorRemainderExpectation
          reference w hw0 hw1 half s hs time)) := by
  let referenceSource := globalCayleyVectorJetBulkReferenceQuadraticSource
    reference s hs (centralExtent half) time
  let remainderSource :=
    globalCayleyVectorJetBulkOuterDenominatorRemainderSource
      reference s hs (centralExtent half) time
  have hcoeff := BF4ExactSlabPolynomialExpectation.expectation_congr
    w hw0 hw1 half
      (globalCayleyVectorJetBulkQuadratic_outerDenominator_split
        reference s hs (centralExtent half) time)
  exact hcoeff.trans (by
    simpa [globalCayleyVectorJetBulkQuadraticExpectation,
      globalCayleyVectorJetBulkReferenceQuadraticExpectation,
      globalCayleyVectorJetBulkOuterDenominatorRemainderExpectation,
      referenceSource, remainderSource] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half referenceSource remainderSource)

/-- Normalized ORIGINAL expectation of the reference-scale source pair. -/
def globalCayleyVectorJetBulkPairReferenceQuadraticExpectation
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairReferenceQuadraticSource
      reference s hs (centralExtent half) leftTime rightTime)

/-- Normalized ORIGINAL expectation of the three pair terms carrying an
outer-denominator deformation. -/
def globalCayleyVectorJetBulkPairOuterDenominatorRemainderExpectation
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairOuterDenominatorRemainderSource
      reference s hs (centralExtent half) leftTime rightTime)

/-- The pair outer-denominator split passes exactly to the normalized ORIGINAL
expectation. -/
theorem globalCayleyVectorJetBulkPairQuadraticExpectation_outerDenominator_split
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkPairQuadraticExpectation
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkPairReferenceQuadraticExpectation
          reference w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkPairOuterDenominatorRemainderExpectation
          reference w hw0 hw1 half s hs leftTime rightTime)) := by
  let referencePair := globalCayleyVectorJetBulkPairReferenceQuadraticSource
    reference s hs (centralExtent half) leftTime rightTime
  let remainderPair :=
    globalCayleyVectorJetBulkPairOuterDenominatorRemainderSource
      reference s hs (centralExtent half) leftTime rightTime
  have hcoeff := BF4ExactSlabPolynomialExpectation.expectation_congr
    w hw0 hw1 half
      (globalCayleyVectorJetBulkPairQuadratic_outerDenominator_split
        reference s hs (centralExtent half) leftTime rightTime)
  exact hcoeff.trans (by
    simpa [globalCayleyVectorJetBulkPairQuadraticExpectation,
      globalCayleyVectorJetBulkPairReferenceQuadraticExpectation,
      globalCayleyVectorJetBulkPairOuterDenominatorRemainderExpectation,
      referencePair, remainderPair] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half referencePair remainderPair)

/-- Centered normalized ORIGINAL response of the two weighted reference-scale
quadratic sources. -/
def globalCayleyVectorJetBulkCenteredReferenceQuadraticResponse
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  CReal.sub
    (globalCayleyVectorJetBulkPairReferenceQuadraticExpectation
      reference w hw0 hw1 half s hs leftTime rightTime)
    (CReal.mul
      (globalCayleyVectorJetBulkReferenceQuadraticExpectation
        reference w hw0 hw1 half s hs leftTime)
      (globalCayleyVectorJetBulkReferenceQuadraticExpectation
        reference w hw0 hw1 half s hs rightTime))

/-- Exact centered correction from the outer-denominator deformation. -/
def globalCayleyVectorJetBulkCenteredOuterDenominatorRemainder
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  let leftReference := globalCayleyVectorJetBulkReferenceQuadraticExpectation
    reference w hw0 hw1 half s hs leftTime
  let rightReference := globalCayleyVectorJetBulkReferenceQuadraticExpectation
    reference w hw0 hw1 half s hs rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkOuterDenominatorRemainderExpectation
      reference w hw0 hw1 half s hs leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkOuterDenominatorRemainderExpectation
      reference w hw0 hw1 half s hs rightTime
  let pairRemainder :=
    globalCayleyVectorJetBulkPairOuterDenominatorRemainderExpectation
      reference w hw0 hw1 half s hs leftTime rightTime
  CReal.sub pairRemainder
    (CReal.add
      (CReal.mul leftReference rightRemainder)
      (CReal.add
        (CReal.mul leftRemainder rightReference)
        (CReal.mul leftRemainder rightRemainder)))

private theorem centeredSplitQ
    (referencePair pairRemainder leftReference leftRemainder
      rightReference rightRemainder : Q') :
    (referencePair + pairRemainder) +
        -((leftReference + leftRemainder) *
          (rightReference + rightRemainder)) ≈
      (referencePair + -(leftReference * rightReference)) +
        (pairRemainder +
          -(leftReference * rightRemainder +
            (leftRemainder * rightReference +
              leftRemainder * rightRemainder))) := by
  let leading := leftReference * rightReference
  let residual := leftReference * rightRemainder +
    (leftRemainder * rightReference + leftRemainder * rightRemainder)
  have hproduct :
      (leftReference + leftRemainder) *
          (rightReference + rightRemainder) ≈
        leading + residual := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv leftReference leftRemainder
        (rightReference + rightRemainder))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv leftReference rightReference rightRemainder)
          (Q'.mul_add_eqv leftRemainder rightReference rightRemainder))
        (Q'.add_assoc_eqv
          (leftReference * rightReference)
          (leftReference * rightRemainder)
          (leftRemainder * rightReference +
            leftRemainder * rightRemainder)))
  have hnegative :
      -((leftReference + leftRemainder) *
          (rightReference + rightRemainder)) ≈
        -leading + -residual :=
    Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ hproduct)
      (Q'.neg_add_eqv leading residual)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hnegative)
    (Q'.add_swap_inner referencePair pairRemainder
      (-leading) (-residual))

/-- The centered weighted quadratic ORIGINAL response splits into the
reference-scale centered response and one explicit outer-denominator
correction, without selecting the reference scale. -/
theorem globalCayleyVectorJetBulkCenteredQuadratic_outerDenominator_split
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredQuadraticResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkCenteredReferenceQuadraticResponse
          reference w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredOuterDenominatorRemainder
          reference w hw0 hw1 half s hs leftTime rightTime)) := by
  let quadraticPair := globalCayleyVectorJetBulkPairQuadraticExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let referencePair :=
    globalCayleyVectorJetBulkPairReferenceQuadraticExpectation
      reference w hw0 hw1 half s hs leftTime rightTime
  let pairRemainder :=
    globalCayleyVectorJetBulkPairOuterDenominatorRemainderExpectation
      reference w hw0 hw1 half s hs leftTime rightTime
  let leftQuadratic := globalCayleyVectorJetBulkQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightQuadratic := globalCayleyVectorJetBulkQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftReference := globalCayleyVectorJetBulkReferenceQuadraticExpectation
    reference w hw0 hw1 half s hs leftTime
  let rightReference := globalCayleyVectorJetBulkReferenceQuadraticExpectation
    reference w hw0 hw1 half s hs rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkOuterDenominatorRemainderExpectation
      reference w hw0 hw1 half s hs leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkOuterDenominatorRemainderExpectation
      reference w hw0 hw1 half s hs rightTime
  have hpair :=
    globalCayleyVectorJetBulkPairQuadraticExpectation_outerDenominator_split
      reference w hw0 hw1 half s hs leftTime rightTime
  change CReal.Equiv quadraticPair
    (CReal.add referencePair pairRemainder) at hpair
  have hleft :=
    globalCayleyVectorJetBulkQuadraticExpectation_outerDenominator_split
      reference w hw0 hw1 half s hs leftTime
  change CReal.Equiv leftQuadratic
    (CReal.add leftReference leftRemainder) at hleft
  have hright :=
    globalCayleyVectorJetBulkQuadraticExpectation_outerDenominator_split
      reference w hw0 hw1 half s hs rightTime
  change CReal.Equiv rightQuadratic
    (CReal.add rightReference rightRemainder) at hright
  have hmeans : CReal.Equiv
      (CReal.mul leftQuadratic rightQuadratic)
      (CReal.mul
        (CReal.add leftReference leftRemainder)
        (CReal.add rightReference rightRemainder)) :=
    Pivot2.mul_congr hleft hright
  have hsub : CReal.Equiv
      (CReal.sub quadraticPair (CReal.mul leftQuadratic rightQuadratic))
      (CReal.sub
        (CReal.add referencePair pairRemainder)
        (CReal.mul
          (CReal.add leftReference leftRemainder)
          (CReal.add rightReference rightRemainder))) :=
    (CReal.sub_congr_left hpair).trans (CReal.sub_congr_right hmeans)
  have hregroup : CReal.Equiv
      (CReal.sub
        (CReal.add referencePair pairRemainder)
        (CReal.mul
          (CReal.add leftReference leftRemainder)
          (CReal.add rightReference rightRemainder)))
      (CReal.add
        (CReal.sub referencePair
          (CReal.mul leftReference rightReference))
        (CReal.sub pairRemainder
          (CReal.add
            (CReal.mul leftReference rightRemainder)
            (CReal.add
              (CReal.mul leftRemainder rightReference)
              (CReal.mul leftRemainder rightRemainder))))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      centeredSplitQ
        (referencePair.approx n) (pairRemainder.approx n)
        (leftReference.approx n) (leftRemainder.approx n)
        (rightReference.approx n) (rightRemainder.approx n))
  change CReal.Equiv
    (CReal.sub quadraticPair (CReal.mul leftQuadratic rightQuadratic)) _
  exact hsub.trans hregroup

/-- Total explicit remainder after replacing the complete cleared centered
response by the centered reference-scale quadratic response. -/
def globalCayleyVectorJetBulkCenteredReferenceTotalRemainder
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  CReal.add
    (globalCayleyVectorJetBulkCenteredOuterDenominatorRemainder
      reference w hw0 hw1 half s hs leftTime rightTime)
    (globalCayleyVectorJetBulkCenteredRemainder
      w hw0 hw1 half s hs leftTime rightTime)

private theorem cadd_assoc (left middle right : CReal) :
    CReal.Equiv
      (CReal.add (CReal.add left middle) right)
      (CReal.add left (CReal.add middle right)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.add_assoc_eqv
      (left.approx n) (middle.approx n) (right.approx n))

/-- Capstone exact split: the complete centered cleared response is the
centered reference-scale quadratic response plus the outer-denominator and
Cayley residuals, under the unchanged normalized ORIGINAL law. -/
theorem globalCayleyVectorJetBulkCentered_reference_total_split
    (reference w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredClearedResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkCenteredReferenceQuadraticResponse
          reference w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredReferenceTotalRemainder
          reference w hw0 hw1 half s hs leftTime rightTime)) := by
  let referenceResponse :=
    globalCayleyVectorJetBulkCenteredReferenceQuadraticResponse
      reference w hw0 hw1 half s hs leftTime rightTime
  let outerRemainder :=
    globalCayleyVectorJetBulkCenteredOuterDenominatorRemainder
      reference w hw0 hw1 half s hs leftTime rightTime
  let cayleyRemainder := globalCayleyVectorJetBulkCenteredRemainder
    w hw0 hw1 half s hs leftTime rightTime
  have hcleared :=
    globalCayleyVectorJetBulkCentered_quadratic_remainder_split
      w hw0 hw1 half s hs leftTime rightTime
        hwidth hleftTime hrightTime
  have houter :=
    globalCayleyVectorJetBulkCenteredQuadratic_outerDenominator_split
      reference w hw0 hw1 half s hs leftTime rightTime
  change CReal.Equiv
    (globalCayleyVectorJetBulkCenteredClearedResponse
      w hw0 hw1 half s hs leftTime rightTime)
    (CReal.add
      (globalCayleyVectorJetBulkCenteredQuadraticResponse
        w hw0 hw1 half s hs leftTime rightTime)
      cayleyRemainder) at hcleared
  change CReal.Equiv
    (globalCayleyVectorJetBulkCenteredQuadraticResponse
      w hw0 hw1 half s hs leftTime rightTime)
    (CReal.add referenceResponse outerRemainder) at houter
  change CReal.Equiv _
    (CReal.add referenceResponse (CReal.add outerRemainder cayleyRemainder))
  exact hcleared.trans
    ((Pivot2.add_congr houter (CReal.Equiv.refl cayleyRemainder)).trans
      (cadd_assoc referenceResponse outerRemainder cayleyRemainder))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator.globalCayleyVectorJetQuadratic_outerDenominator_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator.globalCayleyVectorJetBulkQuadratic_outerDenominator_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator.globalCayleyVectorJetBulkPairQuadratic_outerDenominator_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator.globalCayleyVectorJetBulkQuadraticExpectation_outerDenominator_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator.globalCayleyVectorJetBulkPairQuadraticExpectation_outerDenominator_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator.globalCayleyVectorJetBulkCenteredQuadratic_outerDenominator_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator.globalCayleyVectorJetBulkCentered_reference_total_split
