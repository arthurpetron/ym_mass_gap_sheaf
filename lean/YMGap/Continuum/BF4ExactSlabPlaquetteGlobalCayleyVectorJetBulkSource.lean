/-
# Weighted chronological bulk-source Cayley vector-jet split

The exact global Cayley vector-jet split is summed over the literal finite
bulk face list with its unchanged positive coefficients.  Two chronological
placements are then multiplied, isolating the complete weighted
degree-two--degree-two source pair and one explicit aggregate residual.
One-source and two-source splits pass to the normalized ORIGINAL expectation.

No residual bound, centering identity, denominator removal, FREE Gaussian
comparison, cutoff removal, continuum theory, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetPair
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
import YMGap.Continuum.QuaternionHaarGammaFiniteSum

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetPair
open YMGap.Continuum.QuaternionHaarGammaFiniteSum
  (finitePolySum_add)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Weighted denominator-square-cleared vector-jet source at one
chronological offset. -/
def globalCayleyVectorJetBulkClearedSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetClearedPolynomial extent
        (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

/-- Weighted extracted degree-two source at one chronological offset. -/
def globalCayleyVectorJetBulkQuadraticSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetQuadraticPolynomial extent
        (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

/-- Weighted one-face Cayley residual source at one chronological offset. -/
def globalCayleyVectorJetBulkRemainderSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetRemainderPolynomial extent
        (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

/-- Product of the two literal weighted cleared sources. -/
def globalCayleyVectorJetBulkPairClearedSource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  polyMul
    (globalCayleyVectorJetBulkClearedSource s hs extent leftTime)
    (globalCayleyVectorJetBulkClearedSource s hs extent rightTime)

/-- The three exact aggregate pair products containing at least one weighted
Cayley residual source. -/
def globalCayleyVectorJetBulkPairRemainderSource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  let leftQuadratic :=
    globalCayleyVectorJetBulkQuadraticSource s hs extent leftTime
  let rightQuadratic :=
    globalCayleyVectorJetBulkQuadraticSource s hs extent rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkRemainderSource s hs extent leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkRemainderSource s hs extent rightTime
  polyAdd
    (polyMul leftQuadratic rightRemainder)
    (polyAdd
      (polyMul leftRemainder rightQuadratic)
      (polyMul leftRemainder rightRemainder))

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

/-- Every listed bulk face at the given chronological placement is a physical
face of the ambient ORIGINAL slab. -/
theorem bulkSource_timeShift_physical
    {s extent time : Nat} (hwidth : s * s ≤ extent + 1)
    (htime : time ≤ extent) {face : Z4Plaq}
    (hface : face ∈ bulkSourceFaces s) :
    timeShiftPlaquette time face ∈
      boundaryCompleteSlabPlaquettes extent :=
  spatialFaces_shift_physical hwidth htime
    (bulkSourceFace_mem_spatialFaces_square hface)

/-- The complete literal weighted cleared source is the sum of its weighted
quadratic source and weighted one-face residual source on the full ORIGINAL
carrier. -/
theorem globalCayleyVectorJetBulk_quadratic_remainder_carrier
    {s : Nat} (hs : 0 < s) {extent time : Nat}
    (hwidth : s * s ≤ extent + 1) (htime : time ≤ extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkClearedSource s hs extent time)
      (polyAdd
        (globalCayleyVectorJetBulkQuadraticSource s hs extent time)
        (globalCayleyVectorJetBulkRemainderSource s hs extent time)) := by
  let cleared := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetClearedPolynomial extent
        (timeShiftPlaquette time face))
  let quadratic := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetQuadraticPolynomial extent
        (timeShiftPlaquette time face))
  let remainder := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetRemainderPolynomial extent
        (timeShiftPlaquette time face))
  have hpoint : ∀ face, face ∈ bulkSourceFaces s →
      HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
        (cleared face) (polyAdd (quadratic face) (remainder face)) := by
    intro face hface
    have hsplit := globalCayleyVectorJet_quadratic_remainder_carrier
      (bulkSource_timeShift_physical hwidth htime hface)
    have hscaled := HaarCarrierEqv.smul
      (bulkSourceCoefficient s hs face) hsplit
    exact hscaled.trans (RatPolyCoeffEqv.haarCarrier
      (RatPolyCoeffEqv.smul_add (bulkSourceCoefficient s hs face)
        (globalCayleyVectorJetQuadraticPolynomial extent
          (timeShiftPlaquette time face))
        (globalCayleyVectorJetRemainderPolynomial extent
          (timeShiftPlaquette time face))))
  have hsum := finiteSum_carrier
    (boundaryCompleteSlabLinks extent).length cleared
      (fun face => polyAdd (quadratic face) (remainder face))
      (bulkSourceFaces s) hpoint
  have hseparate := finitePolySum_add quadratic remainder (bulkSourceFaces s)
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (finitePolySum cleared (bulkSourceFaces s))
    (polyAdd
      (finitePolySum quadratic (bulkSourceFaces s))
      (finitePolySum remainder (bulkSourceFaces s)))
  exact hsum.trans (RatPolyCoeffEqv.haarCarrier hseparate)

/-- Exact carrier split of the product of two complete weighted chronological
sources. -/
theorem globalCayleyVectorJetBulkPair_quadratic_remainder_carrier
    {s : Nat} (hs : 0 < s) {extent leftTime rightTime : Nat}
    (hwidth : s * s ≤ extent + 1)
    (hleftTime : leftTime ≤ extent) (hrightTime : rightTime ≤ extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkPairClearedSource
        s hs extent leftTime rightTime)
      (polyAdd
        (polyMul
          (globalCayleyVectorJetBulkQuadraticSource
            s hs extent leftTime)
          (globalCayleyVectorJetBulkQuadraticSource
            s hs extent rightTime))
        (globalCayleyVectorJetBulkPairRemainderSource
          s hs extent leftTime rightTime)) := by
  let leftQuadratic :=
    globalCayleyVectorJetBulkQuadraticSource s hs extent leftTime
  let rightQuadratic :=
    globalCayleyVectorJetBulkQuadraticSource s hs extent rightTime
  let leftRemainder :=
    globalCayleyVectorJetBulkRemainderSource s hs extent leftTime
  let rightRemainder :=
    globalCayleyVectorJetBulkRemainderSource s hs extent rightTime
  have hleft := globalCayleyVectorJetBulk_quadratic_remainder_carrier
    hs hwidth hleftTime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkClearedSource s hs extent leftTime)
    (polyAdd leftQuadratic leftRemainder) at hleft
  have hright := globalCayleyVectorJetBulk_quadratic_remainder_carrier
    hs hwidth hrightTime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkClearedSource s hs extent rightTime)
    (polyAdd rightQuadratic rightRemainder) at hright
  have hproduct := HaarCarrierEqv.mul hleft hright
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkPairClearedSource
      s hs extent leftTime rightTime)
    (polyMul (polyAdd leftQuadratic leftRemainder)
      (polyAdd rightQuadratic rightRemainder)) at hproduct
  have hregroup : RatPolyCoeffEqv
      (polyMul (polyAdd leftQuadratic leftRemainder)
        (polyAdd rightQuadratic rightRemainder))
      (polyAdd (polyMul leftQuadratic rightQuadratic)
        (globalCayleyVectorJetBulkPairRemainderSource
          s hs extent leftTime rightTime)) := by
    unfold globalCayleyVectorJetBulkPairRemainderSource
    have hdistribute : RatPolyCoeffEqv
        (polyMul (polyAdd leftQuadratic leftRemainder)
          (polyAdd rightQuadratic rightRemainder))
        (polyAdd
          (polyAdd
            (polyMul leftQuadratic rightQuadratic)
            (polyMul leftQuadratic rightRemainder))
          (polyAdd
            (polyMul leftRemainder rightQuadratic)
            (polyMul leftRemainder rightRemainder))) := by
      rw [polyMul_add_left_exact]
      exact RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.mul_add_right
          leftQuadratic rightQuadratic rightRemainder)
        (RatPolyCoeffEqv.mul_add_right
          leftRemainder rightQuadratic rightRemainder)
    exact hdistribute.trans
      (RatPolyCoeffEqv.add_assoc
        (polyMul leftQuadratic rightQuadratic)
        (polyMul leftQuadratic rightRemainder)
        (polyAdd
          (polyMul leftRemainder rightQuadratic)
          (polyMul leftRemainder rightRemainder)))
  exact hproduct.trans (RatPolyCoeffEqv.haarCarrier hregroup)

/-- Normalized ORIGINAL expectation of one complete weighted cleared source. -/
def globalCayleyVectorJetBulkClearedExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkClearedSource
      s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of the complete weighted quadratic
source. -/
def globalCayleyVectorJetBulkQuadraticExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkQuadraticSource
      s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of the complete weighted one-face
residual source. -/
def globalCayleyVectorJetBulkRemainderExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkRemainderSource
      s hs (centralExtent half) time)

/-- The exact weighted one-source split passes to the normalized ORIGINAL
expectation and supplies the two mean expansions needed by later centering. -/
theorem globalCayleyVectorJetBulk_originalExpectation_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (htime : time ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkClearedExpectation
        w hw0 hw1 half s hs time)
      (CReal.add
        (globalCayleyVectorJetBulkQuadraticExpectation
          w hw0 hw1 half s hs time)
        (globalCayleyVectorJetBulkRemainderExpectation
          w hw0 hw1 half s hs time)) := by
  let extent := centralExtent half
  let quadratic := globalCayleyVectorJetBulkQuadraticSource
    s hs extent time
  let remainder := globalCayleyVectorJetBulkRemainderSource
    s hs extent time
  have hcarrier := globalCayleyVectorJetBulk_quadratic_remainder_carrier
    hs hwidth htime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkClearedSource s hs extent time)
    (polyAdd quadratic remainder) at hcarrier
  have hcongr := BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half hcarrier
  exact hcongr.trans (by
    simpa [globalCayleyVectorJetBulkClearedExpectation,
      globalCayleyVectorJetBulkQuadraticExpectation,
      globalCayleyVectorJetBulkRemainderExpectation, extent, quadratic,
      remainder] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half quadratic remainder)

/-- Normalized ORIGINAL expectation of the product of two complete weighted
cleared sources. -/
def globalCayleyVectorJetBulkPairClearedExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairClearedSource
      s hs (centralExtent half) leftTime rightTime)

/-- Normalized ORIGINAL expectation of the complete weighted
quadratic--quadratic source product. -/
def globalCayleyVectorJetBulkPairQuadraticExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (polyMul
      (globalCayleyVectorJetBulkQuadraticSource
        s hs (centralExtent half) leftTime)
      (globalCayleyVectorJetBulkQuadraticSource
        s hs (centralExtent half) rightTime))

/-- Normalized ORIGINAL expectation of the three aggregate pair residual
products. -/
def globalCayleyVectorJetBulkPairRemainderExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairRemainderSource
      s hs (centralExtent half) leftTime rightTime)

/-- The exact two-source split passes to the normalized ORIGINAL expectation,
isolating the complete weighted quadratic--quadratic response. -/
theorem globalCayleyVectorJetBulkPair_originalExpectation_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat)
    (hwidth : s * s ≤ centralExtent half + 1)
    (hleftTime : leftTime ≤ centralExtent half)
    (hrightTime : rightTime ≤ centralExtent half) :
    CReal.Equiv
      (globalCayleyVectorJetBulkPairClearedExpectation
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkPairQuadraticExpectation
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkPairRemainderExpectation
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let extent := centralExtent half
  let quadraticPair := polyMul
    (globalCayleyVectorJetBulkQuadraticSource s hs extent leftTime)
    (globalCayleyVectorJetBulkQuadraticSource s hs extent rightTime)
  let remainder := globalCayleyVectorJetBulkPairRemainderSource
    s hs extent leftTime rightTime
  have hcarrier := globalCayleyVectorJetBulkPair_quadratic_remainder_carrier
    hs hwidth hleftTime hrightTime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkPairClearedSource
      s hs extent leftTime rightTime)
    (polyAdd quadraticPair remainder) at hcarrier
  have hcongr := BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half hcarrier
  exact hcongr.trans (by
    simpa [globalCayleyVectorJetBulkPairClearedExpectation,
      globalCayleyVectorJetBulkPairQuadraticExpectation,
      globalCayleyVectorJetBulkPairRemainderExpectation, extent,
      quadraticPair, remainder] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half quadraticPair remainder)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource.bulkSource_timeShift_physical
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource.globalCayleyVectorJetBulk_quadratic_remainder_carrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource.globalCayleyVectorJetBulkPair_quadratic_remainder_carrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource.globalCayleyVectorJetBulk_originalExpectation_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource.globalCayleyVectorJetBulkPair_originalExpectation_split
