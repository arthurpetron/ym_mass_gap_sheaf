/-
# All-chart quadratic mismatch and finite FREE comparison

The quotient-weighted signed-chart quadratic bulk source is compared on its
exact `2^66` normalization with the existing identity-chart quadratic source.
Their full difference is retained as a named source mismatch, propagated
through the pair source, the unchanged normalized ORIGINAL expectation, and
centering.  Combining this comparison with the complete all-chart homogeneous
residual and the existing identity ORIGINAL-to-FREE theorem gives a direct
finite FREE `A2` capstone for the literal centered multi-chart response.

No mismatch or residual is bounded here.  No cutoff removal, continuum
Hamiltonian, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkFreeA2Pullback
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOriginalFreeComparison
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkQuadraticTerms
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleySourceCoefficients
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Full exact difference between the quotient-weighted signed-chart
quadratic bulk source and the identity-chart quadratic bulk source. -/
def globalCayleyVectorJetBulkChartQuadraticMismatchSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  polyAdd
    (globalCayleyVectorJetBulkChartQuadraticSource s hs extent time)
    (polyNeg
      (globalCayleyVectorJetBulkIdentityQuadraticSource s hs extent time))

private theorem splitByDifferenceCoeff (value reference : RatPoly) :
    RatPolyCoeffEqv value
      (polyAdd reference (polyAdd value (polyNeg reference))) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.var 0)
    (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
    (by decide)
    (fun
      | 0 => value
      | _ => reference)

/-- Exact common-normalization source comparison.  The signed-chart
quadratic is the identity quadratic plus the named complete mismatch. -/
theorem globalCayleyVectorJetBulkChartQuadratic_identity_mismatch_split
    (s : Nat) (hs : 0 < s) (extent time : Nat) :
    RatPolyCoeffEqv
      (globalCayleyVectorJetBulkChartQuadraticSource s hs extent time)
      (polyAdd
        (globalCayleyVectorJetBulkIdentityQuadraticSource s hs extent time)
        (globalCayleyVectorJetBulkChartQuadraticMismatchSource
          s hs extent time)) := by
  simpa [globalCayleyVectorJetBulkChartQuadraticMismatchSource] using
    splitByDifferenceCoeff
      (globalCayleyVectorJetBulkChartQuadraticSource s hs extent time)
      (globalCayleyVectorJetBulkIdentityQuadraticSource s hs extent time)

/-- The three chart-quadratic pair products containing at least one complete
chart-versus-identity mismatch source. -/
def globalCayleyVectorJetBulkPairChartQuadraticMismatchSource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  let leftIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs extent leftTime
  let rightIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs extent rightTime
  let leftMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchSource
    s hs extent leftTime
  let rightMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchSource
    s hs extent rightTime
  polyAdd
    (polyMul leftIdentity rightMismatch)
    (polyAdd
      (polyMul leftMismatch rightIdentity)
      (polyMul leftMismatch rightMismatch))

private theorem product_split_coeff
    (leftIdentity leftMismatch rightIdentity rightMismatch : RatPoly) :
    RatPolyCoeffEqv
      (polyMul
        (polyAdd leftIdentity leftMismatch)
        (polyAdd rightIdentity rightMismatch))
      (polyAdd
        (polyMul leftIdentity rightIdentity)
        (polyAdd
          (polyMul leftIdentity rightMismatch)
          (polyAdd
            (polyMul leftMismatch rightIdentity)
            (polyMul leftMismatch rightMismatch)))) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add
      (.mul (.var 0) (.var 2))
      (.add
        (.mul (.var 0) (.var 3))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 3)))))
    (by decide)
    (fun
      | 0 => leftIdentity
      | 1 => leftMismatch
      | 2 => rightIdentity
      | _ => rightMismatch)

/-- Exact pair comparison between the chart-quadratic product and the
identity-quadratic product, retaining all three mismatch-bearing products. -/
theorem globalCayleyVectorJetBulkPairChartQuadratic_identity_mismatch_split
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) :
    RatPolyCoeffEqv
      (globalCayleyVectorJetBulkPairChartQuadraticSource
        s hs extent leftTime rightTime)
      (polyAdd
        (globalCayleyVectorJetBulkPairIdentityQuadraticSource
          s hs extent leftTime rightTime)
        (globalCayleyVectorJetBulkPairChartQuadraticMismatchSource
          s hs extent leftTime rightTime)) := by
  let leftIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs extent leftTime
  let rightIdentity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs extent rightTime
  let leftMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchSource
    s hs extent leftTime
  let rightMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchSource
    s hs extent rightTime
  have hleft := globalCayleyVectorJetBulkChartQuadratic_identity_mismatch_split
    s hs extent leftTime
  change RatPolyCoeffEqv
    (globalCayleyVectorJetBulkChartQuadraticSource s hs extent leftTime)
    (polyAdd leftIdentity leftMismatch) at hleft
  have hright := globalCayleyVectorJetBulkChartQuadratic_identity_mismatch_split
    s hs extent rightTime
  change RatPolyCoeffEqv
    (globalCayleyVectorJetBulkChartQuadraticSource s hs extent rightTime)
    (polyAdd rightIdentity rightMismatch) at hright
  have hproduct := RatPolyCoeffEqv.mul hleft hright
  change RatPolyCoeffEqv
    (globalCayleyVectorJetBulkPairChartQuadraticSource
      s hs extent leftTime rightTime)
    (polyMul (polyAdd leftIdentity leftMismatch)
      (polyAdd rightIdentity rightMismatch)) at hproduct
  exact hproduct.trans
    (product_split_coeff leftIdentity leftMismatch
      rightIdentity rightMismatch)

/-- Normalized ORIGINAL expectation of one complete chart-quadratic mismatch
source. -/
def globalCayleyVectorJetBulkChartQuadraticMismatchExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkChartQuadraticMismatchSource
      s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of the three chart-quadratic pair terms
containing at least one mismatch source. -/
def globalCayleyVectorJetBulkPairChartQuadraticMismatchExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairChartQuadraticMismatchSource
      s hs (centralExtent half) leftTime rightTime)

/-- The one-source chart-versus-identity comparison passes through the
unchanged normalized ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkChartQuadraticExpectation_identity_mismatch_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkChartQuadraticExpectation
        w hw0 hw1 half s hs time)
      (CReal.add
        (globalCayleyVectorJetBulkIdentityQuadraticExpectation
          w hw0 hw1 half s hs time)
        (globalCayleyVectorJetBulkChartQuadraticMismatchExpectation
          w hw0 hw1 half s hs time)) := by
  let chart := globalCayleyVectorJetBulkChartQuadraticSource
    s hs (centralExtent half) time
  let identity := globalCayleyVectorJetBulkIdentityQuadraticSource
    s hs (centralExtent half) time
  let mismatch := globalCayleyVectorJetBulkChartQuadraticMismatchSource
    s hs (centralExtent half) time
  have hcoeff := BF4ExactSlabPolynomialExpectation.expectation_congr
    w hw0 hw1 half
      (globalCayleyVectorJetBulkChartQuadratic_identity_mismatch_split
        s hs (centralExtent half) time)
  change CReal.Equiv
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half chart)
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
      (polyAdd identity mismatch)) at hcoeff
  exact hcoeff.trans (by
    simpa [globalCayleyVectorJetBulkChartQuadraticExpectation,
      globalCayleyVectorJetBulkIdentityQuadraticExpectation,
      globalCayleyVectorJetBulkChartQuadraticMismatchExpectation,
      chart, identity, mismatch] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half identity mismatch)

/-- The pair chart-versus-identity comparison passes through the same
normalized ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkPairChartQuadraticExpectation_identity_mismatch_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkPairChartQuadraticExpectation
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkPairIdentityQuadraticExpectation
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkPairChartQuadraticMismatchExpectation
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let chartPair := globalCayleyVectorJetBulkPairChartQuadraticSource
    s hs (centralExtent half) leftTime rightTime
  let identityPair := globalCayleyVectorJetBulkPairIdentityQuadraticSource
    s hs (centralExtent half) leftTime rightTime
  let mismatchPair := globalCayleyVectorJetBulkPairChartQuadraticMismatchSource
    s hs (centralExtent half) leftTime rightTime
  have hcoeff := BF4ExactSlabPolynomialExpectation.expectation_congr
    w hw0 hw1 half
      (globalCayleyVectorJetBulkPairChartQuadratic_identity_mismatch_split
        s hs (centralExtent half) leftTime rightTime)
  change CReal.Equiv
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half chartPair)
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
      (polyAdd identityPair mismatchPair)) at hcoeff
  exact hcoeff.trans (by
    simpa [globalCayleyVectorJetBulkPairChartQuadraticExpectation,
      globalCayleyVectorJetBulkPairIdentityQuadraticExpectation,
      globalCayleyVectorJetBulkPairChartQuadraticMismatchExpectation,
      chartPair, identityPair, mismatchPair] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half identityPair mismatchPair)

/-- Complete centered chart-versus-identity quadratic mismatch.  The pair
term and both one-source mean corrections remain under the same ORIGINAL
normalization. -/
def globalCayleyVectorJetBulkCenteredChartQuadraticMismatch
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  let leftIdentity := globalCayleyVectorJetBulkIdentityQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightIdentity := globalCayleyVectorJetBulkIdentityQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchExpectation
    w hw0 hw1 half s hs leftTime
  let rightMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchExpectation
    w hw0 hw1 half s hs rightTime
  let pairMismatch :=
    globalCayleyVectorJetBulkPairChartQuadraticMismatchExpectation
      w hw0 hw1 half s hs leftTime rightTime
  CReal.sub pairMismatch
    (CReal.add
      (CReal.mul leftIdentity rightMismatch)
      (CReal.add
        (CReal.mul leftMismatch rightIdentity)
        (CReal.mul leftMismatch rightMismatch)))

private theorem centeredSplitQ
    (identityPair pairMismatch leftIdentity leftMismatch
      rightIdentity rightMismatch : Q') :
    (identityPair + pairMismatch) +
        -((leftIdentity + leftMismatch) *
          (rightIdentity + rightMismatch)) ≈
      (identityPair + -(leftIdentity * rightIdentity)) +
        (pairMismatch +
          -(leftIdentity * rightMismatch +
            (leftMismatch * rightIdentity +
              leftMismatch * rightMismatch))) := by
  exact poly_identity_of_normal_eq
    (.add
      (.add (.var 0) (.var 1))
      (.neg (.mul (.add (.var 2) (.var 3))
        (.add (.var 4) (.var 5)))))
    (.add
      (.add (.var 0) (.neg (.mul (.var 2) (.var 4))))
      (.add (.var 1)
        (.neg
          (.add
            (.mul (.var 2) (.var 5))
            (.add (.mul (.var 3) (.var 4))
              (.mul (.var 3) (.var 5)))))))
    (by decide)
    (fun
      | 0 => identityPair
      | 1 => pairMismatch
      | 2 => leftIdentity
      | 3 => leftMismatch
      | 4 => rightIdentity
      | _ => rightMismatch)

/-- Exact centered common-normalization comparison: the all-chart quadratic
response is the identity-quadratic ORIGINAL response plus the full named
chart mismatch. -/
theorem globalCayleyVectorJetBulkCenteredChartQuadratic_identity_mismatch_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredChartQuadraticResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkCenteredIdentityQuadraticResponse
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredChartQuadraticMismatch
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let chartPair := globalCayleyVectorJetBulkPairChartQuadraticExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let identityPair := globalCayleyVectorJetBulkPairIdentityQuadraticExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let pairMismatch :=
    globalCayleyVectorJetBulkPairChartQuadraticMismatchExpectation
      w hw0 hw1 half s hs leftTime rightTime
  let leftChart := globalCayleyVectorJetBulkChartQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightChart := globalCayleyVectorJetBulkChartQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftIdentity := globalCayleyVectorJetBulkIdentityQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightIdentity := globalCayleyVectorJetBulkIdentityQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchExpectation
    w hw0 hw1 half s hs leftTime
  let rightMismatch := globalCayleyVectorJetBulkChartQuadraticMismatchExpectation
    w hw0 hw1 half s hs rightTime
  have hpair :=
    globalCayleyVectorJetBulkPairChartQuadraticExpectation_identity_mismatch_split
      w hw0 hw1 half s hs leftTime rightTime
  change CReal.Equiv chartPair
    (CReal.add identityPair pairMismatch) at hpair
  have hleft :=
    globalCayleyVectorJetBulkChartQuadraticExpectation_identity_mismatch_split
      w hw0 hw1 half s hs leftTime
  change CReal.Equiv leftChart
    (CReal.add leftIdentity leftMismatch) at hleft
  have hright :=
    globalCayleyVectorJetBulkChartQuadraticExpectation_identity_mismatch_split
      w hw0 hw1 half s hs rightTime
  change CReal.Equiv rightChart
    (CReal.add rightIdentity rightMismatch) at hright
  have hmeans : CReal.Equiv
      (CReal.mul leftChart rightChart)
      (CReal.mul
        (CReal.add leftIdentity leftMismatch)
        (CReal.add rightIdentity rightMismatch)) :=
    Pivot2.mul_congr hleft hright
  have hsub : CReal.Equiv
      (CReal.sub chartPair (CReal.mul leftChart rightChart))
      (CReal.sub
        (CReal.add identityPair pairMismatch)
        (CReal.mul
          (CReal.add leftIdentity leftMismatch)
          (CReal.add rightIdentity rightMismatch))) :=
    (CReal.sub_congr_left hpair).trans (CReal.sub_congr_right hmeans)
  have hregroup : CReal.Equiv
      (CReal.sub
        (CReal.add identityPair pairMismatch)
        (CReal.mul
          (CReal.add leftIdentity leftMismatch)
          (CReal.add rightIdentity rightMismatch)))
      (CReal.add
        (CReal.sub identityPair
          (CReal.mul leftIdentity rightIdentity))
        (CReal.sub pairMismatch
          (CReal.add
            (CReal.mul leftIdentity rightMismatch)
            (CReal.add
              (CReal.mul leftMismatch rightIdentity)
              (CReal.mul leftMismatch rightMismatch))))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      centeredSplitQ
        (identityPair.approx n) (pairMismatch.approx n)
        (leftIdentity.approx n) (leftMismatch.approx n)
        (rightIdentity.approx n) (rightMismatch.approx n))
  change CReal.Equiv
    (CReal.sub chartPair (CReal.mul leftChart rightChart)) _
  exact hsub.trans hregroup

/-- Complete remainder in the direct literal multi-chart ORIGINAL-to-FREE
comparison.  It contains exactly the ORIGINAL-to-FREE law defect, the centered
chart-quadratic mismatch, and the complete centered all-chart homogeneous
residual. -/
def globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat) : CReal :=
  CReal.add
    (globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonRemainder
      w hw0 hw1 half s hs stage leftTime rightTime)
    (CReal.add
      (globalCayleyVectorJetBulkCenteredChartQuadraticMismatch
        w hw0 hw1 half s hs leftTime rightTime)
      (globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual
        w hw0 hw1 half s hs leftTime rightTime))

private theorem cadd_four_assoc
    (first second third fourth : CReal) :
    CReal.Equiv
      (CReal.add (CReal.add (CReal.add first second) third) fourth)
      (CReal.add first
        (CReal.add second (CReal.add third fourth))) := by
  exact SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.add (.var 0) (.add (.var 1) (.add (.var 2) (.var 3))))
      (by decide)
      (fun
        | 0 => (first.approx n)
        | 1 => (second.approx n)
        | 2 => (third.approx n)
        | _ => (fourth.approx n)))

/-- Direct finite FREE comparison for the literal centered multi-chart
response.  Only the three explicitly named residual families remain. -/
theorem globalCayleyVectorJetBulkCenteredMultiChart_freeComparison_total_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredMultiChartReassemblyResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
          half s hs stage leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual
          w hw0 hw1 half s hs stage leftTime rightTime)) := by
  let multiChart :=
    globalCayleyVectorJetBulkCenteredMultiChartReassemblyResponse
      w hw0 hw1 half s hs leftTime rightTime
  let chart := globalCayleyVectorJetBulkCenteredChartQuadraticResponse
    w hw0 hw1 half s hs leftTime rightTime
  let homogeneous :=
    globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual
      w hw0 hw1 half s hs leftTime rightTime
  let identity := globalCayleyVectorJetBulkCenteredIdentityQuadraticResponse
    w hw0 hw1 half s hs leftTime rightTime
  let mismatch := globalCayleyVectorJetBulkCenteredChartQuadraticMismatch
    w hw0 hw1 half s hs leftTime rightTime
  let free := globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance
    half s hs stage leftTime rightTime
  let comparison :=
    globalCayleyVectorJetBulkCenteredOriginalToFreeComparisonRemainder
      w hw0 hw1 half s hs stage leftTime rightTime
  have hhomogeneous :=
    globalCayleyVectorJetBulkCenteredMultiChartReassembly_chartHomogeneous
      w hw0 hw1 half s hs leftTime rightTime
        hwidth hleftTime hrightTime
  change CReal.Equiv multiChart (CReal.add chart homogeneous) at hhomogeneous
  have hmismatch :=
    globalCayleyVectorJetBulkCenteredChartQuadratic_identity_mismatch_split
      w hw0 hw1 half s hs leftTime rightTime
  change CReal.Equiv chart (CReal.add identity mismatch) at hmismatch
  have hcomparison :=
    globalCayleyVectorJetBulkCenteredIdentity_original_free_split
      w hw0 hw1 half s hs stage leftTime rightTime
  change CReal.Equiv identity (CReal.add free comparison) at hcomparison
  change CReal.Equiv multiChart
    (CReal.add free
      (CReal.add comparison (CReal.add mismatch homogeneous)))
  exact hhomogeneous.trans
    ((Pivot2.add_congr hmismatch (CReal.Equiv.refl homogeneous)).trans
      ((Pivot2.add_congr
        (Pivot2.add_congr hcomparison (CReal.Equiv.refl mismatch))
        (CReal.Equiv.refl homogeneous)).trans
        (cadd_four_assoc free comparison mismatch homogeneous)))

/-- The leading finite FREE term in the direct multi-chart comparison is
exactly the existing scaled FREE `A2` covariance. -/
theorem globalCayleyVectorJetBulkCenteredMultiChart_freeA2_total_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (stage leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredMultiChartReassemblyResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (CReal.ofQ'
          ((identityCayleyVectorJetFreeA2Scale *
            identityCayleyVectorJetFreeA2Scale) *
            finiteGaussianCovariance
              (bulkSourceNoiseCount (centralExtent half) s)
              (openCubeBulkCayleyTraceA2
                (centralExtent half) s hs stage leftTime)
              (openCubeBulkCayleyTraceA2
                (centralExtent half) s hs stage rightTime)))
        (globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual
          w hw0 hw1 half s hs stage leftTime rightTime)) := by
  have hsplit :=
    globalCayleyVectorJetBulkCenteredMultiChart_freeComparison_total_split
      w hw0 hw1 half s hs stage leftTime rightTime
        hwidth hleftTime hrightTime
  have hA2 := globalCayleyVectorJetBulkIdentityQuadraticFiniteFreeCovariance_eq_A2
    half s hs stage leftTime rightTime
  exact hsplit.trans
    (Pivot2.add_congr hA2
      (CReal.Equiv.refl
        (globalCayleyVectorJetBulkCenteredMultiChartFreeTotalResidual
          w hw0 hw1 half s hs stage leftTime rightTime)))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison.globalCayleyVectorJetBulkChartQuadratic_identity_mismatch_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison.globalCayleyVectorJetBulkPairChartQuadratic_identity_mismatch_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison.globalCayleyVectorJetBulkChartQuadraticExpectation_identity_mismatch_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison.globalCayleyVectorJetBulkPairChartQuadraticExpectation_identity_mismatch_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison.globalCayleyVectorJetBulkCenteredChartQuadratic_identity_mismatch_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison.globalCayleyVectorJetBulkCenteredMultiChart_freeComparison_total_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkFreeComparison.globalCayleyVectorJetBulkCenteredMultiChart_freeA2_total_split
