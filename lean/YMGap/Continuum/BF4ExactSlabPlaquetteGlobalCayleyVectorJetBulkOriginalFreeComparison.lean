/-
# Exact ORIGINAL-to-FREE comparison remainder for the Cayley vector jet

The canonical reference-scale ORIGINAL quadratic response still contains the
inner Cayley-denominator deformation isolated previously.  This leaf passes
that split through the unchanged normalized ORIGINAL expectation and
centering, then places the exact finite FREE covariance from the physical-link
Heron pullback beside the identity-quadratic ORIGINAL response.

The difference between those two laws is retained as a named comparison
remainder.  Combining the identities gives one exact capstone whose leading
term is the finite FREE covariance and whose remainder contains, separately,
the ORIGINAL-to-FREE comparison error, inner-denominator deformation,
outer-denominator deformation, and complete centered Cayley residual.

No comparison error is bounded here.  In particular, no gauge-fixing
pushforward, density comparison, cutoff-uniform estimate, continuum theory,
or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityDenominator
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Product of the two literal weighted identity-quadratic ORIGINAL
sources. -/
def globalCayleyVectorJetBulkPairIdentityQuadraticSource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  polyMul
    (globalCayleyVectorJetBulkIdentityQuadraticSource
      s hs extent leftTime)
    (globalCayleyVectorJetBulkIdentityQuadraticSource
      s hs extent rightTime)

/-- The three products containing at least one inner-denominator deformation
source. -/
def globalCayleyVectorJetBulkPairInnerDenominatorRemainderSource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  let leftIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs extent leftTime
  let rightIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs extent rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkInnerDenominatorRemainderSource
      s hs extent leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkInnerDenominatorRemainderSource
      s hs extent rightTime
  polyAdd
    (polyMul leftIdentity rightRemainder)
    (polyAdd
      (polyMul leftRemainder rightIdentity)
      (polyMul leftRemainder rightRemainder))

/-- Exact pair split of the canonical reference-scale source into the
identity quadratic pair and every product carrying an inner deformation. -/
theorem globalCayleyVectorJetBulkPairReferenceQuadratic_identity_inner_split
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) :
    RatPolyCoeffEqv
      (globalCayleyVectorJetBulkPairReferenceQuadraticSource
        identityCayleyDenominatorReference
        s hs extent leftTime rightTime)
      (polyAdd
        (globalCayleyVectorJetBulkPairIdentityQuadraticSource
          s hs extent leftTime rightTime)
        (globalCayleyVectorJetBulkPairInnerDenominatorRemainderSource
          s hs extent leftTime rightTime)) := by
  let leftIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs extent leftTime
  let rightIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs extent rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkInnerDenominatorRemainderSource
      s hs extent leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkInnerDenominatorRemainderSource
      s hs extent rightTime
  have hleft := globalCayleyVectorJetBulkReferenceQuadratic_identity_inner_split
    s hs extent leftTime
  change RatPolyCoeffEqv
    (globalCayleyVectorJetBulkReferenceQuadraticSource
      identityCayleyDenominatorReference s hs extent leftTime)
    (polyAdd leftIdentity leftRemainder) at hleft
  have hright := globalCayleyVectorJetBulkReferenceQuadratic_identity_inner_split
    s hs extent rightTime
  change RatPolyCoeffEqv
    (globalCayleyVectorJetBulkReferenceQuadraticSource
      identityCayleyDenominatorReference s hs extent rightTime)
    (polyAdd rightIdentity rightRemainder) at hright
  have hproduct := RatPolyCoeffEqv.mul hleft hright
  have hdistribute : RatPolyCoeffEqv
      (polyMul (polyAdd leftIdentity leftRemainder)
        (polyAdd rightIdentity rightRemainder))
      (polyAdd
        (polyAdd
          (polyMul leftIdentity rightIdentity)
          (polyMul leftIdentity rightRemainder))
        (polyAdd
          (polyMul leftRemainder rightIdentity)
          (polyMul leftRemainder rightRemainder))) := by
    rw [polyMul_add_left_exact]
    exact RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.mul_add_right
        leftIdentity rightIdentity rightRemainder)
      (RatPolyCoeffEqv.mul_add_right
        leftRemainder rightIdentity rightRemainder)
  exact hproduct.trans (hdistribute.trans
    (RatPolyCoeffEqv.add_assoc
      (polyMul leftIdentity rightIdentity)
      (polyMul leftIdentity rightRemainder)
      (polyAdd
        (polyMul leftRemainder rightIdentity)
        (polyMul leftRemainder rightRemainder))))

/-- Normalized ORIGINAL expectation of one weighted identity-quadratic
source. -/
def globalCayleyVectorJetBulkIdentityQuadraticExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkIdentityQuadraticSource
      s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of one weighted inner-denominator
deformation source. -/
def globalCayleyVectorJetBulkInnerDenominatorRemainderExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkInnerDenominatorRemainderSource
      s hs (centralExtent half) time)

/-- The one-source inner-denominator split passes exactly to the normalized
ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkReferenceQuadraticExpectation_identity_inner_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkReferenceQuadraticExpectation
        identityCayleyDenominatorReference
        w hw0 hw1 half s hs time)
      (CReal.add
        (globalCayleyVectorJetBulkIdentityQuadraticExpectation
          w hw0 hw1 half s hs time)
        (globalCayleyVectorJetBulkInnerDenominatorRemainderExpectation
          w hw0 hw1 half s hs time)) := by
  let identitySource := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs (centralExtent half) time
  let remainderSource :=
    globalCayleyVectorJetBulkInnerDenominatorRemainderSource
      s hs (centralExtent half) time
  have hcoeff := BF4ExactSlabPolynomialExpectation.expectation_congr
    w hw0 hw1 half
      (globalCayleyVectorJetBulkReferenceQuadratic_identity_inner_split
        s hs (centralExtent half) time)
  exact hcoeff.trans (by
    simpa [globalCayleyVectorJetBulkReferenceQuadraticExpectation,
      globalCayleyVectorJetBulkIdentityQuadraticExpectation,
      globalCayleyVectorJetBulkInnerDenominatorRemainderExpectation,
      identitySource, remainderSource] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half identitySource remainderSource)

/-- Normalized ORIGINAL expectation of the weighted identity-quadratic source
pair. -/
def globalCayleyVectorJetBulkPairIdentityQuadraticExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairIdentityQuadraticSource
      s hs (centralExtent half) leftTime rightTime)

/-- Normalized ORIGINAL expectation of the three pair products carrying an
inner-denominator deformation. -/
def globalCayleyVectorJetBulkPairInnerDenominatorRemainderExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairInnerDenominatorRemainderSource
      s hs (centralExtent half) leftTime rightTime)

/-- The pair inner-denominator split passes exactly to the normalized
ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkPairReferenceQuadraticExpectation_identity_inner_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkPairReferenceQuadraticExpectation
        identityCayleyDenominatorReference
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkPairIdentityQuadraticExpectation
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkPairInnerDenominatorRemainderExpectation
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let identityPair := globalCayleyVectorJetBulkPairIdentityQuadraticSource
    s hs (centralExtent half) leftTime rightTime
  let remainderPair :=
    globalCayleyVectorJetBulkPairInnerDenominatorRemainderSource
      s hs (centralExtent half) leftTime rightTime
  have hcoeff := BF4ExactSlabPolynomialExpectation.expectation_congr
    w hw0 hw1 half
      (globalCayleyVectorJetBulkPairReferenceQuadratic_identity_inner_split
        s hs (centralExtent half) leftTime rightTime)
  exact hcoeff.trans (by
    simpa [globalCayleyVectorJetBulkPairReferenceQuadraticExpectation,
      globalCayleyVectorJetBulkPairIdentityQuadraticExpectation,
      globalCayleyVectorJetBulkPairInnerDenominatorRemainderExpectation,
      identityPair, remainderPair] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half identityPair remainderPair)

/-- Centered normalized ORIGINAL response of the two identity-quadratic
sources. -/
def globalCayleyVectorJetBulkCenteredIdentityQuadraticResponse
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  CReal.sub
    (globalCayleyVectorJetBulkPairIdentityQuadraticExpectation
      w hw0 hw1 half s hs leftTime rightTime)
    (CReal.mul
      (globalCayleyVectorJetBulkIdentityQuadraticExpectation
        w hw0 hw1 half s hs leftTime)
      (globalCayleyVectorJetBulkIdentityQuadraticExpectation
        w hw0 hw1 half s hs rightTime))

/-- Exact centered correction contributed by the inner Cayley-denominator
deformation. -/
def globalCayleyVectorJetBulkCenteredInnerDenominatorRemainder
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  let leftIdentity := globalCayleyVectorJetBulkIdentityQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightIdentity := globalCayleyVectorJetBulkIdentityQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkInnerDenominatorRemainderExpectation
      w hw0 hw1 half s hs leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkInnerDenominatorRemainderExpectation
      w hw0 hw1 half s hs rightTime
  let pairRemainder :=
    globalCayleyVectorJetBulkPairInnerDenominatorRemainderExpectation
      w hw0 hw1 half s hs leftTime rightTime
  CReal.sub pairRemainder
    (CReal.add
      (CReal.mul leftIdentity rightRemainder)
      (CReal.add
        (CReal.mul leftRemainder rightIdentity)
        (CReal.mul leftRemainder rightRemainder)))

private theorem centeredSplitQ
    (identityPair pairRemainder leftIdentity leftRemainder
      rightIdentity rightRemainder : Q') :
    (identityPair + pairRemainder) +
        -((leftIdentity + leftRemainder) *
          (rightIdentity + rightRemainder)) ≈
      (identityPair + -(leftIdentity * rightIdentity)) +
        (pairRemainder +
          -(leftIdentity * rightRemainder +
            (leftRemainder * rightIdentity +
              leftRemainder * rightRemainder))) := by
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1))
      (.neg (.mul (.add (.var 2) (.var 3))
        (.add (.var 4) (.var 5)))))
    (.add (.add (.var 0) (.neg (.mul (.var 2) (.var 4))))
      (.add (.var 1)
        (.neg (.add (.mul (.var 2) (.var 5))
          (.add (.mul (.var 3) (.var 4))
            (.mul (.var 3) (.var 5)))))))
    (by decide) (fun
      | 0 => identityPair
      | 1 => pairRemainder
      | 2 => leftIdentity
      | 3 => leftRemainder
      | 4 => rightIdentity
      | _ => rightRemainder)

/-- The centered canonical reference-scale ORIGINAL response splits into the
centered identity quadratic response and the complete centered inner
denominator correction. -/
theorem globalCayleyVectorJetBulkCenteredReference_identity_inner_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredReferenceQuadraticResponse
        identityCayleyDenominatorReference
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkCenteredIdentityQuadraticResponse
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredInnerDenominatorRemainder
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let referencePair :=
    globalCayleyVectorJetBulkPairReferenceQuadraticExpectation
      identityCayleyDenominatorReference
      w hw0 hw1 half s hs leftTime rightTime
  let identityPair := globalCayleyVectorJetBulkPairIdentityQuadraticExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let pairRemainder :=
    globalCayleyVectorJetBulkPairInnerDenominatorRemainderExpectation
      w hw0 hw1 half s hs leftTime rightTime
  let leftReference := globalCayleyVectorJetBulkReferenceQuadraticExpectation
    identityCayleyDenominatorReference
    w hw0 hw1 half s hs leftTime
  let rightReference := globalCayleyVectorJetBulkReferenceQuadraticExpectation
    identityCayleyDenominatorReference
    w hw0 hw1 half s hs rightTime
  let leftIdentity := globalCayleyVectorJetBulkIdentityQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightIdentity := globalCayleyVectorJetBulkIdentityQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkInnerDenominatorRemainderExpectation
      w hw0 hw1 half s hs leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkInnerDenominatorRemainderExpectation
      w hw0 hw1 half s hs rightTime
  have hpair :=
    globalCayleyVectorJetBulkPairReferenceQuadraticExpectation_identity_inner_split
      w hw0 hw1 half s hs leftTime rightTime
  change CReal.Equiv referencePair
    (CReal.add identityPair pairRemainder) at hpair
  have hleft :=
    globalCayleyVectorJetBulkReferenceQuadraticExpectation_identity_inner_split
      w hw0 hw1 half s hs leftTime
  change CReal.Equiv leftReference
    (CReal.add leftIdentity leftRemainder) at hleft
  have hright :=
    globalCayleyVectorJetBulkReferenceQuadraticExpectation_identity_inner_split
      w hw0 hw1 half s hs rightTime
  change CReal.Equiv rightReference
    (CReal.add rightIdentity rightRemainder) at hright
  have hmeans : CReal.Equiv
      (CReal.mul leftReference rightReference)
      (CReal.mul
        (CReal.add leftIdentity leftRemainder)
        (CReal.add rightIdentity rightRemainder)) :=
    Pivot2.mul_congr hleft hright
  have hsub : CReal.Equiv
      (CReal.sub referencePair (CReal.mul leftReference rightReference))
      (CReal.sub
        (CReal.add identityPair pairRemainder)
        (CReal.mul
          (CReal.add leftIdentity leftRemainder)
          (CReal.add rightIdentity rightRemainder))) :=
    (CReal.sub_congr_left hpair).trans (CReal.sub_congr_right hmeans)
  have hregroup : CReal.Equiv
      (CReal.sub
        (CReal.add identityPair pairRemainder)
        (CReal.mul
          (CReal.add leftIdentity leftRemainder)
          (CReal.add rightIdentity rightRemainder)))
      (CReal.add
        (CReal.sub identityPair
          (CReal.mul leftIdentity rightIdentity))
        (CReal.sub pairRemainder
          (CReal.add
            (CReal.mul leftIdentity rightRemainder)
            (CReal.add
              (CReal.mul leftRemainder rightIdentity)
              (CReal.mul leftRemainder rightRemainder))))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      centeredSplitQ
        (identityPair.approx n) (pairRemainder.approx n)
        (leftIdentity.approx n) (leftRemainder.approx n)
        (rightIdentity.approx n) (rightRemainder.approx n))
  change CReal.Equiv
    (CReal.sub referencePair (CReal.mul leftReference rightReference)) _
  exact hsub.trans hregroup

/-- Canonical finite FREE covariance of the physical-link pullback at the
same finite central extent and the requested rational Heron stage. -/
def globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) : CReal :=
  CReal.ofQ'
    (finiteGaussianCovariance
      (bulkSourceNoiseCount (centralExtent half) s)
      (globalCayleyVectorJetBulkIdentityQuadraticFreePullback
        (centralExtent half) s hs stage leftTime)
      (globalCayleyVectorJetBulkIdentityQuadraticFreePullback
        (centralExtent half) s hs stage rightTime))

/-- The displayed FREE comparison term is exactly the scaled covariance of
the existing FREE `A2` sources. -/
theorem globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance_eq_A2
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
        half s hs stage leftTime rightTime)
      (CReal.ofQ'
        ((identityCayleyVectorJetFreeA2Scale *
          identityCayleyVectorJetFreeA2Scale) *
          finiteGaussianCovariance
            (bulkSourceNoiseCount (centralExtent half) s)
            (openCubeBulkCayleyTraceA2
              (centralExtent half) s hs stage leftTime)
            (openCubeBulkCayleyTraceA2
              (centralExtent half) s hs stage rightTime))) := by
  exact CReal.ofQ'_equiv_of_eqv
    (finiteGaussianCovariance_globalIdentityQuadraticFreePullback_eq_A2
      (centralExtent half) s hs stage leftTime rightTime)

/-- Complete finite ORIGINAL-to-FREE comparison defect for the centered
identity-quadratic response.  No sign or size is assumed. -/
def globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonRemainder
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) : CReal :=
  CReal.sub
    (globalCayleyVectorJetBulkCenteredIdentityQuadraticResponse
      w hw0 hw1 half s hs leftTime rightTime)
    (globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
      half s hs stage leftTime rightTime)

private theorem splitByDifferenceQ (value reference : Q') :
    value ≈ reference + (value + -reference) :=
  poly_identity_of_normal_eq
    (.var 0)
    (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
    (by decide) (fun
      | 0 => value
      | _ => reference)

/-- Exact comparison split.  This theorem names the full difference; it does
not estimate or erase it. -/
theorem globalCayleyVectorJetBulkCenteredIdentity_original_free_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredIdentityQuadraticResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
          half s hs stage leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonRemainder
          w hw0 hw1 half s hs stage leftTime rightTime)) := by
  exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
    splitByDifferenceQ
      ((globalCayleyVectorJetBulkCenteredIdentityQuadraticResponse
        w hw0 hw1 half s hs leftTime rightTime).approx n)
      ((globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
        half s hs stage leftTime rightTime).approx n))

/-- Complete named remainder after replacing the centered cleared ORIGINAL
response by the finite FREE identity-quadratic covariance. -/
def globalCayleyVectorJetBulkCenteredFreeComparisonTotalRemainder
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) : CReal :=
  CReal.add
    (globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonRemainder
      w hw0 hw1 half s hs stage leftTime rightTime)
    (CReal.add
      (globalCayleyVectorJetBulkCenteredInnerDenominatorRemainder
        w hw0 hw1 half s hs leftTime rightTime)
      (globalCayleyVectorJetBulkCenteredReferenceTotalRemainder
        identityCayleyDenominatorReference
        w hw0 hw1 half s hs leftTime rightTime))

private theorem cadd_assoc (left middle right : CReal) :
    CReal.Equiv
      (CReal.add (CReal.add left middle) right)
      (CReal.add left (CReal.add middle right)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.add_assoc_eqv
      (left.approx n) (middle.approx n) (right.approx n))

private theorem cadd_four_assoc
    (first second third fourth : CReal) :
    CReal.Equiv
      (CReal.add (CReal.add (CReal.add first second) third) fourth)
      (CReal.add first
        (CReal.add second (CReal.add third fourth))) := by
  exact (Pivot2.add_congr
      (cadd_assoc first second third) (CReal.Equiv.refl fourth)).trans
    ((cadd_assoc first (CReal.add second third) fourth).trans
      (Pivot2.add_congr (CReal.Equiv.refl first)
        (cadd_assoc second third fourth)))

/-- Exact four-error capstone.  The complete centered cleared ORIGINAL
response equals the finite FREE covariance plus the named comparison, inner,
outer and Cayley remainders, with no term discarded. -/
theorem globalCayleyVectorJetBulkCentered_freeComparison_total_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredClearedResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
          half s hs stage leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredFreeComparisonTotalRemainder
          w hw0 hw1 half s hs stage leftTime rightTime)) := by
  let free := globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
    half s hs stage leftTime rightTime
  let comparison :=
    globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonRemainder
      w hw0 hw1 half s hs stage leftTime rightTime
  let identity := globalCayleyVectorJetBulkCenteredIdentityQuadraticResponse
    w hw0 hw1 half s hs leftTime rightTime
  let inner := globalCayleyVectorJetBulkCenteredInnerDenominatorRemainder
    w hw0 hw1 half s hs leftTime rightTime
  let reference :=
    globalCayleyVectorJetBulkCenteredReferenceQuadraticResponse
      identityCayleyDenominatorReference
      w hw0 hw1 half s hs leftTime rightTime
  let outerCayley := globalCayleyVectorJetBulkCenteredReferenceTotalRemainder
    identityCayleyDenominatorReference
    w hw0 hw1 half s hs leftTime rightTime
  have hcleared :=
    globalCayleyVectorJetBulkCentered_identityDenominator_total_split
      w hw0 hw1 half s hs leftTime rightTime
      hwidth hleftTime hrightTime
  change CReal.Equiv
    (globalCayleyVectorJetBulkCenteredClearedResponse
      w hw0 hw1 half s hs leftTime rightTime)
    (CReal.add reference outerCayley) at hcleared
  have hinner :=
    globalCayleyVectorJetBulkCenteredReference_identity_inner_split
      w hw0 hw1 half s hs leftTime rightTime
  change CReal.Equiv reference (CReal.add identity inner) at hinner
  have hcomparison :=
    globalCayleyVectorJetBulkCenteredIdentity_original_free_split
      w hw0 hw1 half s hs stage leftTime rightTime
  change CReal.Equiv identity (CReal.add free comparison) at hcomparison
  change CReal.Equiv _
    (CReal.add free
      (CReal.add comparison (CReal.add inner outerCayley)))
  exact hcleared.trans
    ((Pivot2.add_congr hinner (CReal.Equiv.refl outerCayley)).trans
      ((Pivot2.add_congr
        (Pivot2.add_congr hcomparison (CReal.Equiv.refl inner))
        (CReal.Equiv.refl outerCayley)).trans
        (cadd_four_assoc free comparison inner outerCayley)))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison.globalCayleyVectorJetBulkPairReferenceQuadratic_identity_inner_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison.globalCayleyVectorJetBulkCenteredReference_identity_inner_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison.globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance_eq_A2
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison.globalCayleyVectorJetBulkCenteredIdentity_original_free_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison.globalCayleyVectorJetBulkCentered_freeComparison_total_split
