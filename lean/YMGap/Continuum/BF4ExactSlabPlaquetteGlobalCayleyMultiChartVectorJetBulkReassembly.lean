/-
# Lossless multi-chart reassembly of the centered ORIGINAL bulk vector jet

The facewise sixteen-chart Haar-carrier identity is lifted through the literal
weighted chronological bulk source, its pair source, the unchanged normalized
ORIGINAL expectation, and centering.  The resulting multi-chart centered
response is exactly the identity-scaled pure ORIGINAL vector-jet response;
there is no single-chart north-weight deficit.

This is an exact finite reassembly.  It does not bound the chartwise Cayley
remainders, compare the ORIGINAL and FREE laws, remove a cutoff, construct a
continuum Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- The literal weighted chronological source formed from the complete
sixteen-chart facewise reassembly. -/
def globalCayleyVectorJetBulkMultiChartReassemblySource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleySignedChartReassemblyPolynomial extent
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

/-- The complete multi-chart bulk source is the existing identity-scaled pure
bulk source on the same finite ORIGINAL Haar carrier. -/
theorem globalCayleyVectorJetBulkMultiChartReassembly_carrier_pure
    (s : Nat) (hs : 0 < s) (extent time : Nat) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkMultiChartReassemblySource
        s hs extent time)
      (globalCayleyVectorJetBulkIdentityScaledPureSource
        s hs extent time) := by
  let reassembled := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleySignedChartReassemblyPolynomial extent
        (timeShiftPlaquette time face))
  let pure := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetIdentityScaledPurePolynomial extent
        (timeShiftPlaquette time face))
  have hpoint : ∀ face, face ∈ bulkSourceFaces s →
      HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
        (reassembled face) (pure face) := by
    intro face _
    have hface :=
      globalCayleySignedChartReassembly_carrier_identityScaled
        extent (timeShiftPlaquette time face)
    have hscaled := HaarCarrierEqv.smul
      (bulkSourceCoefficient s hs face) hface
    simpa [reassembled, pure,
      globalCayleyVectorJetIdentityScaledPurePolynomial,
      globalCayleyVectorJetNorthWeightScale] using hscaled
  exact finiteSum_carrier
    (boundaryCompleteSlabLinks extent).length reassembled pure
    (bulkSourceFaces s) hpoint

/-- Product of the left and right multi-chart reassembled bulk sources. -/
def globalCayleyVectorJetBulkPairMultiChartReassemblySource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  polyMul
    (globalCayleyVectorJetBulkMultiChartReassemblySource
      s hs extent leftTime)
    (globalCayleyVectorJetBulkMultiChartReassemblySource
      s hs extent rightTime)

/-- The multi-chart pair source is the identity-scaled pure pair source on the
same finite ORIGINAL Haar carrier. -/
theorem globalCayleyVectorJetBulkPairMultiChartReassembly_carrier_pure
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkPairMultiChartReassemblySource
        s hs extent leftTime rightTime)
      (globalCayleyVectorJetBulkPairIdentityScaledPureSource
        s hs extent leftTime rightTime) := by
  exact HaarCarrierEqv.mul
    (globalCayleyVectorJetBulkMultiChartReassembly_carrier_pure
      s hs extent leftTime)
    (globalCayleyVectorJetBulkMultiChartReassembly_carrier_pure
      s hs extent rightTime)

/-- Normalized ORIGINAL expectation of one multi-chart reassembled source. -/
def globalCayleyVectorJetBulkMultiChartReassemblyExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkMultiChartReassemblySource
      s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of the multi-chart pair source. -/
def globalCayleyVectorJetBulkPairMultiChartReassemblyExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairMultiChartReassemblySource
      s hs (centralExtent half) leftTime rightTime)

/-- The one-source multi-chart reassembly passes through the unchanged
normalized ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkMultiChartReassemblyExpectation_pure
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkMultiChartReassemblyExpectation
        w hw0 hw1 half s hs time)
      (globalCayleyVectorJetBulkIdentityScaledPureExpectation
        w hw0 hw1 half s hs time) := by
  exact BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half
    (globalCayleyVectorJetBulkMultiChartReassembly_carrier_pure
      s hs (centralExtent half) time)

/-- The pair multi-chart reassembly passes through the same normalized
ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkPairMultiChartReassemblyExpectation_pure
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkPairMultiChartReassemblyExpectation
        w hw0 hw1 half s hs leftTime rightTime)
      (globalCayleyVectorJetBulkPairIdentityScaledPureExpectation
        w hw0 hw1 half s hs leftTime rightTime) := by
  exact BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half
    (globalCayleyVectorJetBulkPairMultiChartReassembly_carrier_pure
      s hs (centralExtent half) leftTime rightTime)

/-- Centered normalized ORIGINAL response formed from the complete
multi-chart reassembled sources. -/
def globalCayleyVectorJetBulkCenteredMultiChartReassemblyResponse
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  CReal.sub
    (globalCayleyVectorJetBulkPairMultiChartReassemblyExpectation
      w hw0 hw1 half s hs leftTime rightTime)
    (CReal.mul
      (globalCayleyVectorJetBulkMultiChartReassemblyExpectation
        w hw0 hw1 half s hs leftTime)
      (globalCayleyVectorJetBulkMultiChartReassemblyExpectation
        w hw0 hw1 half s hs rightTime))

/-- Lossless centered lift: the complete multi-chart response is exactly the
identity-scaled pure ORIGINAL response, with no north-weight deficit. -/
theorem globalCayleyVectorJetBulkCenteredMultiChartReassembly_pure
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredMultiChartReassemblyResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
        w hw0 hw1 half s hs leftTime rightTime) := by
  have hpair :=
    globalCayleyVectorJetBulkPairMultiChartReassemblyExpectation_pure
      w hw0 hw1 half s hs leftTime rightTime
  have hleft :=
    globalCayleyVectorJetBulkMultiChartReassemblyExpectation_pure
      w hw0 hw1 half s hs leftTime
  have hright :=
    globalCayleyVectorJetBulkMultiChartReassemblyExpectation_pure
      w hw0 hw1 half s hs rightTime
  have hmeans := Pivot2.mul_congr hleft hright
  exact (CReal.sub_congr_left hpair).trans
    (CReal.sub_congr_right hmeans)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly.globalCayleyVectorJetBulkMultiChartReassembly_carrier_pure
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly.globalCayleyVectorJetBulkPairMultiChartReassembly_carrier_pure
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly.globalCayleyVectorJetBulkMultiChartReassemblyExpectation_pure
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly.globalCayleyVectorJetBulkPairMultiChartReassemblyExpectation_pure
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkReassembly.globalCayleyVectorJetBulkCenteredMultiChartReassembly_pure
