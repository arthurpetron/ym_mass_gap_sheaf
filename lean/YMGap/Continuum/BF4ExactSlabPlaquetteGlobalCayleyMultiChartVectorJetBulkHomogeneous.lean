/-
# Centered bulk lift of the all-chart homogeneous Cayley split

The exact quotient-weighted signed-chart quadratic/residual decomposition is
summed over the literal weighted chronological source, multiplied in two time
slots, passed through the unchanged normalized ORIGINAL expectation, and
centered.  The centered residual keeps the three products containing at least
one all-chart homogeneous remainder and both one-source center corrections.

This is an exact finite algebraic decomposition.  It does not bound the
residual, compare the chart quadratic with the FREE Gaussian response, remove
a cutoff, construct a continuum Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetHomogeneous
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetHomogeneous
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource
open YMGap.Continuum.QuaternionHaarGammaFiniteSum
  (finitePolySum_add)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- Literal weighted chronological source of the quotient-weighted signed-chart
quadratic aggregate. -/
def globalCayleyVectorJetBulkChartQuadraticSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleySignedChartQuadraticReassemblyPolynomial extent
        (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

/-- Literal weighted chronological source of the complete quotient-weighted
all-chart homogeneous remainder. -/
def globalCayleyVectorJetBulkChartRemainderSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleySignedChartRemainderReassemblyPolynomial extent
        (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

private theorem finiteSum_carrier
    {Index : Type} (blocks : Nat) (left right : Index → RatPoly) :
    ∀ items : List Index,
      (∀ index, index ∈ items →
        HaarCarrierEqv blocks (left index) (right index)) →
      HaarCarrierEqv blocks
        (finitePolySum left items) (finitePolySum right items)
  | [], _ => HaarCarrierEqv.refl _ _
  | index :: items, h =>
      HaarCarrierEqv.add (h index List.mem_cons_self)
        (finiteSum_carrier blocks left right items
          (fun next hnext => h next (List.mem_cons_of_mem index hnext)))

/-- The identity-scaled pure weighted bulk source is exactly the all-chart
quadratic source plus the complete all-chart homogeneous remainder on the
same finite ORIGINAL Haar carrier. -/
theorem globalCayleyVectorJetBulkIdentityScaledPure_carrier_chartHomogeneous
    {s : Nat} (hs : 0 < s) {extent time : Nat}
    (hwidth : s * s ≤ extent + 1) (htime : time ≤ extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkIdentityScaledPureSource
        s hs extent time)
      (polyAdd
        (globalCayleyVectorJetBulkChartQuadraticSource
          s hs extent time)
        (globalCayleyVectorJetBulkChartRemainderSource
          s hs extent time)) := by
  let pure := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetIdentityScaledPurePolynomial extent
        (timeShiftPlaquette time face))
  let quadratic := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleySignedChartQuadraticReassemblyPolynomial extent
        (timeShiftPlaquette time face))
  let remainder := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleySignedChartRemainderReassemblyPolynomial extent
        (timeShiftPlaquette time face))
  have hpoint : ∀ face, face ∈ bulkSourceFaces s →
      HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
        (pure face) (polyAdd (quadratic face) (remainder face)) := by
    intro face hface
    have hsplit :=
      globalCayleySignedChartHomogeneousReassembly_carrier_identityScaled
        (bulkSource_timeShift_physical hwidth htime hface)
    have hpure : HaarCarrierEqv
        (boundaryCompleteSlabLinks extent).length
        (globalCayleyVectorJetIdentityScaledPurePolynomial extent
          (timeShiftPlaquette time face))
        (polyAdd
          (globalCayleySignedChartQuadraticReassemblyPolynomial extent
            (timeShiftPlaquette time face))
          (globalCayleySignedChartRemainderReassemblyPolynomial extent
            (timeShiftPlaquette time face))) := by
      simpa [globalCayleyVectorJetIdentityScaledPurePolynomial,
        globalCayleyVectorJetNorthWeightScale] using hsplit
    have hscaled := HaarCarrierEqv.smul
      (bulkSourceCoefficient s hs face) hpure
    exact hscaled.trans (RatPolyCoeffEqv.haarCarrier
      (RatPolyCoeffEqv.smul_add (bulkSourceCoefficient s hs face)
        (globalCayleySignedChartQuadraticReassemblyPolynomial extent
          (timeShiftPlaquette time face))
        (globalCayleySignedChartRemainderReassemblyPolynomial extent
          (timeShiftPlaquette time face))))
  have hsum := finiteSum_carrier
    (boundaryCompleteSlabLinks extent).length pure
    (fun face => polyAdd (quadratic face) (remainder face))
    (bulkSourceFaces s) hpoint
  have hseparate := finitePolySum_add quadratic remainder (bulkSourceFaces s)
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (finitePolySum pure (bulkSourceFaces s))
    (polyAdd
      (finitePolySum quadratic (bulkSourceFaces s))
      (finitePolySum remainder (bulkSourceFaces s)))
  exact hsum.trans (RatPolyCoeffEqv.haarCarrier hseparate)

/-- The literal multi-chart reassembled source has the same exact all-chart
quadratic/remainder split. -/
theorem globalCayleyVectorJetBulkMultiChartReassembly_carrier_chartHomogeneous
    {s : Nat} (hs : 0 < s) {extent time : Nat}
    (hwidth : s * s ≤ extent + 1) (htime : time ≤ extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkMultiChartReassemblySource
        s hs extent time)
      (polyAdd
        (globalCayleyVectorJetBulkChartQuadraticSource
          s hs extent time)
        (globalCayleyVectorJetBulkChartRemainderSource
          s hs extent time)) :=
  (globalCayleyVectorJetBulkMultiChartReassembly_carrier_pure
    s hs extent time).trans
      (globalCayleyVectorJetBulkIdentityScaledPure_carrier_chartHomogeneous
        hs hwidth htime)

/-- Product of the left and right all-chart quadratic bulk sources. -/
def globalCayleyVectorJetBulkPairChartQuadraticSource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  polyMul
    (globalCayleyVectorJetBulkChartQuadraticSource
      s hs extent leftTime)
    (globalCayleyVectorJetBulkChartQuadraticSource
      s hs extent rightTime)

/-- The three pair-source products containing at least one complete all-chart
homogeneous remainder. -/
def globalCayleyVectorJetBulkPairChartRemainderSource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  let leftQuadratic := globalCayleyVectorJetBulkChartQuadraticSource
    s hs extent leftTime
  let rightQuadratic := globalCayleyVectorJetBulkChartQuadraticSource
    s hs extent rightTime
  let leftRemainder := globalCayleyVectorJetBulkChartRemainderSource
    s hs extent leftTime
  let rightRemainder := globalCayleyVectorJetBulkChartRemainderSource
    s hs extent rightTime
  polyAdd
    (polyMul leftQuadratic rightRemainder)
    (polyAdd
      (polyMul leftRemainder rightQuadratic)
      (polyMul leftRemainder rightRemainder))

private theorem product_split_coeff
    (leftQuadratic leftRemainder rightQuadratic rightRemainder : RatPoly) :
    RatPolyCoeffEqv
      (polyMul
        (polyAdd leftQuadratic leftRemainder)
        (polyAdd rightQuadratic rightRemainder))
      (polyAdd
        (polyMul leftQuadratic rightQuadratic)
        (polyAdd
          (polyMul leftQuadratic rightRemainder)
          (polyAdd
            (polyMul leftRemainder rightQuadratic)
            (polyMul leftRemainder rightRemainder)))) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add
      (.mul (.var 0) (.var 2))
      (.add
        (.mul (.var 0) (.var 3))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 3)))))
    (by decide)
    (fun
      | 0 => leftQuadratic
      | 1 => leftRemainder
      | 2 => rightQuadratic
      | _ => rightRemainder)

/-- The identity-scaled pure pair source is the chart-quadratic pair plus
exactly the three products carrying an all-chart homogeneous remainder. -/
theorem globalCayleyVectorJetBulkPairIdentityScaledPure_carrier_chartHomogeneous
    {s : Nat} (hs : 0 < s) {extent leftTime rightTime : Nat}
    (hwidth : s * s ≤ extent + 1)
    (hleftTime : leftTime ≤ extent) (hrightTime : rightTime ≤ extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkPairIdentityScaledPureSource
        s hs extent leftTime rightTime)
      (polyAdd
        (globalCayleyVectorJetBulkPairChartQuadraticSource
          s hs extent leftTime rightTime)
        (globalCayleyVectorJetBulkPairChartRemainderSource
          s hs extent leftTime rightTime)) := by
  let leftQuadratic := globalCayleyVectorJetBulkChartQuadraticSource
    s hs extent leftTime
  let rightQuadratic := globalCayleyVectorJetBulkChartQuadraticSource
    s hs extent rightTime
  let leftRemainder := globalCayleyVectorJetBulkChartRemainderSource
    s hs extent leftTime
  let rightRemainder := globalCayleyVectorJetBulkChartRemainderSource
    s hs extent rightTime
  have hleft :=
    globalCayleyVectorJetBulkIdentityScaledPure_carrier_chartHomogeneous
      hs hwidth hleftTime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkIdentityScaledPureSource
      s hs extent leftTime)
    (polyAdd leftQuadratic leftRemainder) at hleft
  have hright :=
    globalCayleyVectorJetBulkIdentityScaledPure_carrier_chartHomogeneous
      hs hwidth hrightTime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkIdentityScaledPureSource
      s hs extent rightTime)
    (polyAdd rightQuadratic rightRemainder) at hright
  have hproduct := HaarCarrierEqv.mul hleft hright
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkPairIdentityScaledPureSource
      s hs extent leftTime rightTime)
    (polyMul (polyAdd leftQuadratic leftRemainder)
      (polyAdd rightQuadratic rightRemainder)) at hproduct
  exact hproduct.trans (RatPolyCoeffEqv.haarCarrier
    (product_split_coeff leftQuadratic leftRemainder
      rightQuadratic rightRemainder))

/-- The literal multi-chart pair source has the same exact all-chart
quadratic/remainder split. -/
theorem globalCayleyVectorJetBulkPairMultiChartReassembly_carrier_chartHomogeneous
    {s : Nat} (hs : 0 < s) {extent leftTime rightTime : Nat}
    (hwidth : s * s ≤ extent + 1)
    (hleftTime : leftTime ≤ extent) (hrightTime : rightTime ≤ extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkPairMultiChartReassemblySource
        s hs extent leftTime rightTime)
      (polyAdd
        (globalCayleyVectorJetBulkPairChartQuadraticSource
          s hs extent leftTime rightTime)
        (globalCayleyVectorJetBulkPairChartRemainderSource
          s hs extent leftTime rightTime)) :=
  (globalCayleyVectorJetBulkPairMultiChartReassembly_carrier_pure
    s hs extent leftTime rightTime).trans
      (globalCayleyVectorJetBulkPairIdentityScaledPure_carrier_chartHomogeneous
        hs hwidth hleftTime hrightTime)

/-- Normalized ORIGINAL expectation of one all-chart quadratic bulk source. -/
def globalCayleyVectorJetBulkChartQuadraticExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkChartQuadraticSource
      s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of one complete all-chart homogeneous
remainder source. -/
def globalCayleyVectorJetBulkChartRemainderExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkChartRemainderSource
      s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of the all-chart quadratic pair. -/
def globalCayleyVectorJetBulkPairChartQuadraticExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairChartQuadraticSource
      s hs (centralExtent half) leftTime rightTime)

/-- Normalized ORIGINAL expectation of the three pair terms containing at
least one complete all-chart homogeneous remainder. -/
def globalCayleyVectorJetBulkPairChartRemainderExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairChartRemainderSource
      s hs (centralExtent half) leftTime rightTime)

/-- The one-source all-chart homogeneous split passes through the unchanged
normalized ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkIdentityScaledPureExpectation_chartHomogeneous
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (htime : time ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkIdentityScaledPureExpectation
        w hw0 hw1 half s hs time)
      (CReal.add
        (globalCayleyVectorJetBulkChartQuadraticExpectation
          w hw0 hw1 half s hs time)
        (globalCayleyVectorJetBulkChartRemainderExpectation
          w hw0 hw1 half s hs time)) := by
  let extent := centralExtent half
  let pure := globalCayleyVectorJetBulkIdentityScaledPureSource
    s hs extent time
  let quadratic := globalCayleyVectorJetBulkChartQuadraticSource
    s hs extent time
  let remainder := globalCayleyVectorJetBulkChartRemainderSource
    s hs extent time
  have hcarrier :=
    globalCayleyVectorJetBulkIdentityScaledPure_carrier_chartHomogeneous
      hs hwidth htime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    pure (polyAdd quadratic remainder) at hcarrier
  have hcongr := BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half hcarrier
  change CReal.Equiv
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half pure)
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
      (polyAdd quadratic remainder)) at hcongr
  exact hcongr.trans (by
    simpa [globalCayleyVectorJetBulkIdentityScaledPureExpectation,
      globalCayleyVectorJetBulkChartQuadraticExpectation,
      globalCayleyVectorJetBulkChartRemainderExpectation,
      extent, pure, quadratic, remainder] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half quadratic remainder)

/-- The pair all-chart homogeneous split passes through the same normalized
ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkPairIdentityScaledPureExpectation_chartHomogeneous
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkPairIdentityScaledPureExpectation
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkPairChartQuadraticExpectation
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkPairChartRemainderExpectation
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let extent := centralExtent half
  let purePair := globalCayleyVectorJetBulkPairIdentityScaledPureSource
    s hs extent leftTime rightTime
  let quadraticPair := globalCayleyVectorJetBulkPairChartQuadraticSource
    s hs extent leftTime rightTime
  let remainderPair := globalCayleyVectorJetBulkPairChartRemainderSource
    s hs extent leftTime rightTime
  have hcarrier :=
    globalCayleyVectorJetBulkPairIdentityScaledPure_carrier_chartHomogeneous
      hs hwidth hleftTime hrightTime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    purePair (polyAdd quadraticPair remainderPair) at hcarrier
  have hcongr := BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half hcarrier
  change CReal.Equiv
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half purePair)
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
      (polyAdd quadraticPair remainderPair)) at hcongr
  exact hcongr.trans (by
    simpa [globalCayleyVectorJetBulkPairIdentityScaledPureExpectation,
      globalCayleyVectorJetBulkPairChartQuadraticExpectation,
      globalCayleyVectorJetBulkPairChartRemainderExpectation,
      extent, purePair, quadraticPair, remainderPair] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half quadraticPair remainderPair)

/-- Centered normalized ORIGINAL response of the all-chart quadratic bulk
sources. -/
def globalCayleyVectorJetBulkCenteredChartQuadraticResponse
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  CReal.sub
    (globalCayleyVectorJetBulkPairChartQuadraticExpectation
      w hw0 hw1 half s hs leftTime rightTime)
    (CReal.mul
      (globalCayleyVectorJetBulkChartQuadraticExpectation
        w hw0 hw1 half s hs leftTime)
      (globalCayleyVectorJetBulkChartQuadraticExpectation
        w hw0 hw1 half s hs rightTime))

/-- Complete centered all-chart homogeneous residual.  The pair term contains
all three products with at least one remainder, and the subtracted means keep
both one-source centers under the same ORIGINAL normalization. -/
def globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  let leftQuadratic := globalCayleyVectorJetBulkChartQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightQuadratic := globalCayleyVectorJetBulkChartQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftRemainder := globalCayleyVectorJetBulkChartRemainderExpectation
    w hw0 hw1 half s hs leftTime
  let rightRemainder := globalCayleyVectorJetBulkChartRemainderExpectation
    w hw0 hw1 half s hs rightTime
  let pairRemainder := globalCayleyVectorJetBulkPairChartRemainderExpectation
    w hw0 hw1 half s hs leftTime rightTime
  CReal.sub pairRemainder
    (CReal.add
      (CReal.mul leftQuadratic rightRemainder)
      (CReal.add
        (CReal.mul leftRemainder rightQuadratic)
        (CReal.mul leftRemainder rightRemainder)))

private theorem centeredSplitQ
    (quadraticPair pairRemainder leftQuadratic leftRemainder
      rightQuadratic rightRemainder : Q') :
    (quadraticPair + pairRemainder) +
        -((leftQuadratic + leftRemainder) *
          (rightQuadratic + rightRemainder)) ≈
      (quadraticPair + -(leftQuadratic * rightQuadratic)) +
        (pairRemainder +
          -(leftQuadratic * rightRemainder +
            (leftRemainder * rightQuadratic +
              leftRemainder * rightRemainder))) := by
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
      | 0 => quadraticPair
      | 1 => pairRemainder
      | 2 => leftQuadratic
      | 3 => leftRemainder
      | 4 => rightQuadratic
      | _ => rightRemainder)

/-- Exact centered split of the identity-scaled pure ORIGINAL response into
the all-chart quadratic response and the complete centered homogeneous
residual. -/
theorem globalCayleyVectorJetBulkCenteredIdentityScaledPure_chartHomogeneous
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkCenteredChartQuadraticResponse
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let purePair := globalCayleyVectorJetBulkPairIdentityScaledPureExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let quadraticPair := globalCayleyVectorJetBulkPairChartQuadraticExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let pairRemainder := globalCayleyVectorJetBulkPairChartRemainderExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let leftPure := globalCayleyVectorJetBulkIdentityScaledPureExpectation
    w hw0 hw1 half s hs leftTime
  let rightPure := globalCayleyVectorJetBulkIdentityScaledPureExpectation
    w hw0 hw1 half s hs rightTime
  let leftQuadratic := globalCayleyVectorJetBulkChartQuadraticExpectation
    w hw0 hw1 half s hs leftTime
  let rightQuadratic := globalCayleyVectorJetBulkChartQuadraticExpectation
    w hw0 hw1 half s hs rightTime
  let leftRemainder := globalCayleyVectorJetBulkChartRemainderExpectation
    w hw0 hw1 half s hs leftTime
  let rightRemainder := globalCayleyVectorJetBulkChartRemainderExpectation
    w hw0 hw1 half s hs rightTime
  have hpair :=
    globalCayleyVectorJetBulkPairIdentityScaledPureExpectation_chartHomogeneous
      w hw0 hw1 half s hs leftTime rightTime
        hwidth hleftTime hrightTime
  change CReal.Equiv purePair
    (CReal.add quadraticPair pairRemainder) at hpair
  have hleft :=
    globalCayleyVectorJetBulkIdentityScaledPureExpectation_chartHomogeneous
      w hw0 hw1 half s hs leftTime hwidth hleftTime
  change CReal.Equiv leftPure
    (CReal.add leftQuadratic leftRemainder) at hleft
  have hright :=
    globalCayleyVectorJetBulkIdentityScaledPureExpectation_chartHomogeneous
      w hw0 hw1 half s hs rightTime hwidth hrightTime
  change CReal.Equiv rightPure
    (CReal.add rightQuadratic rightRemainder) at hright
  have hmeans : CReal.Equiv
      (CReal.mul leftPure rightPure)
      (CReal.mul
        (CReal.add leftQuadratic leftRemainder)
        (CReal.add rightQuadratic rightRemainder)) :=
    Pivot2.mul_congr hleft hright
  have hsub : CReal.Equiv
      (CReal.sub purePair (CReal.mul leftPure rightPure))
      (CReal.sub
        (CReal.add quadraticPair pairRemainder)
        (CReal.mul
          (CReal.add leftQuadratic leftRemainder)
          (CReal.add rightQuadratic rightRemainder))) :=
    (CReal.sub_congr_left hpair).trans (CReal.sub_congr_right hmeans)
  have hregroup : CReal.Equiv
      (CReal.sub
        (CReal.add quadraticPair pairRemainder)
        (CReal.mul
          (CReal.add leftQuadratic leftRemainder)
          (CReal.add rightQuadratic rightRemainder)))
      (CReal.add
        (CReal.sub quadraticPair
          (CReal.mul leftQuadratic rightQuadratic))
        (CReal.sub pairRemainder
          (CReal.add
            (CReal.mul leftQuadratic rightRemainder)
            (CReal.add
              (CReal.mul leftRemainder rightQuadratic)
              (CReal.mul leftRemainder rightRemainder))))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      centeredSplitQ
        (quadraticPair.approx n) (pairRemainder.approx n)
        (leftQuadratic.approx n) (leftRemainder.approx n)
        (rightQuadratic.approx n) (rightRemainder.approx n))
  change CReal.Equiv
    (CReal.sub purePair (CReal.mul leftPure rightPure)) _
  exact hsub.trans hregroup

/-- The literal centered multi-chart reassembly has the same exact all-chart
quadratic response plus complete centered homogeneous residual. -/
theorem globalCayleyVectorJetBulkCenteredMultiChartReassembly_chartHomogeneous
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredMultiChartReassemblyResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkCenteredChartQuadraticResponse
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredAllChartHomogeneousResidual
          w hw0 hw1 half s hs leftTime rightTime)) :=
  (globalCayleyVectorJetBulkCenteredMultiChartReassembly_pure
    w hw0 hw1 half s hs leftTime rightTime).trans
      (globalCayleyVectorJetBulkCenteredIdentityScaledPure_chartHomogeneous
        w hw0 hw1 half s hs leftTime rightTime
          hwidth hleftTime hrightTime)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous.globalCayleyVectorJetBulkIdentityScaledPure_carrier_chartHomogeneous
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous.globalCayleyVectorJetBulkMultiChartReassembly_carrier_chartHomogeneous
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous.globalCayleyVectorJetBulkPairIdentityScaledPure_carrier_chartHomogeneous
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous.globalCayleyVectorJetBulkPairMultiChartReassembly_carrier_chartHomogeneous
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous.globalCayleyVectorJetBulkIdentityScaledPureExpectation_chartHomogeneous
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous.globalCayleyVectorJetBulkPairIdentityScaledPureExpectation_chartHomogeneous
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous.globalCayleyVectorJetBulkCenteredIdentityScaledPure_chartHomogeneous
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkHomogeneous.globalCayleyVectorJetBulkCenteredMultiChartReassembly_chartHomogeneous
