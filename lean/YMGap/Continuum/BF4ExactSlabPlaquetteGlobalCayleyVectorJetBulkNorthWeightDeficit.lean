/-
# Exact centered north-weight deficit for the ORIGINAL bulk vector jet

The exact normalized north-chart factor from the preceding leaf is inserted
into the complete weighted bulk source.  The identity-scaled pure ORIGINAL
vector jet is the cleared source plus one explicit source containing the
literal factor `1 - P^14` on every face.  The same split is propagated through
the pair source and both one-source means under one unchanged normalized
ORIGINAL action.

No absolute-value estimate, southern-tail bound, multi-chart partition,
ORIGINAL-to-FREE comparison, cutoff-uniform estimate, continuum theory, or
mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkSource
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkCentered
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic
open YMGap.Continuum.QuaternionHaarGammaFiniteSum
  (finitePolySum_add)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- The exact `2^66` scale shared by the normalized north weight and the
fully identity-normalized quadratic source. -/
def globalCayleyVectorJetNorthWeightScale : Q' :=
  Q'.ofInt (2 ^ 66)

/-- The north-weight scale is the existing combined outer/inner identity
quadratic scale. -/
theorem globalCayleyVectorJetNorthWeightScale_eq_identity :
    globalCayleyVectorJetNorthWeightScale ≈
      identityCayleyVectorJetQuadraticScale := by
  exact Q'.eqv_trans _ _ _
    (by decide : globalCayleyVectorJetNorthWeightScale ≈
      Q'.ofNat 73786976294838206464)
    identityCayleyVectorJetQuadraticScale_eq_pow.symm

/-- The pure ORIGINAL plaquette vector jet at the exact identity scale. -/
def globalCayleyVectorJetIdentityScaledPurePolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polySmul globalCayleyVectorJetNorthWeightScale polyOne)
    (globalPlaquetteVectorJet extent face)

/-- The literal single-north-chart loss.  Its first nonconstant factor is
exactly `1 - P^14`; no division by the north weight occurs. -/
def globalCayleyVectorJetNorthWeightDeficitPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polySmul globalCayleyVectorJetNorthWeightScale polyOne)
    (polyMul
      (polyAdd polyOne
        (polyNeg (globalCayleyNorthBasePower14 extent face)))
      (globalPlaquetteVectorJet extent face))

private theorem identity_weight_deficit_coeff
    (weight vectorJet : RatPoly) :
    RatPolyCoeffEqv
      (polyMul
        (polySmul globalCayleyVectorJetNorthWeightScale polyOne)
        vectorJet)
      (polyAdd
        (polyMul
          (polyMul
            (polySmul globalCayleyVectorJetNorthWeightScale polyOne)
            weight)
          vectorJet)
        (polyMul
          (polySmul globalCayleyVectorJetNorthWeightScale polyOne)
          (polyMul (polyAdd polyOne (polyNeg weight)) vectorJet))) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.var 2))
    (.add
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0)
        (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))))
    (by decide)
    (fun
      | 0 => polySmul globalCayleyVectorJetNorthWeightScale polyOne
      | 1 => weight
      | _ => vectorJet)

/-- On every physical face, the identity-scaled pure vector jet is the actual
cleared vector jet plus the explicit `1 - P^14` deficit. -/
theorem globalCayleyVectorJetIdentityScaledPure_carrier_cleared_deficit
    (extent : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetIdentityScaledPurePolynomial extent face)
      (polyAdd
        (globalCayleyVectorJetClearedPolynomial extent face)
        (globalCayleyVectorJetNorthWeightDeficitPolynomial extent face)) := by
  let weight := globalCayleyNorthBasePower14 extent face
  let vectorJet := globalPlaquetteVectorJet extent face
  let scaledWeight := globalCayleyNorthScaledBasePower14 extent face
  let deficit := globalCayleyVectorJetNorthWeightDeficitPolynomial extent face
  have hcoeff := identity_weight_deficit_coeff weight vectorJet
  change RatPolyCoeffEqv
    (globalCayleyVectorJetIdentityScaledPurePolynomial extent face)
    (polyAdd (polyMul scaledWeight vectorJet) deficit) at hcoeff
  have hcleared :=
    globalCayleyVectorJetClearedPolynomial_carrier_scaledBasePower14
      extent face
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetClearedPolynomial extent face)
    (polyMul scaledWeight vectorJet) at hcleared
  exact (RatPolyCoeffEqv.haarCarrier hcoeff).trans
    (HaarCarrierEqv.add hcleared.symm
      (HaarCarrierEqv.refl _ deficit))

/-- Identity-scaled pure ORIGINAL bulk vector-jet source at one chronological
placement. -/
def globalCayleyVectorJetBulkIdentityScaledPureSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetIdentityScaledPurePolynomial extent
        (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

/-- Bulk source carrying the exact facewise factor `1 - P^14`. -/
def globalCayleyVectorJetBulkNorthWeightDeficitSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetNorthWeightDeficitPolynomial extent
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

/-- The complete identity-scaled pure bulk source is the actual cleared bulk
source plus the exact north-weight deficit, on the same slab Haar carrier. -/
theorem globalCayleyVectorJetBulkIdentityScaledPure_carrier_cleared_deficit
    (s : Nat) (hs : 0 < s) (extent time : Nat) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkIdentityScaledPureSource
        s hs extent time)
      (polyAdd
        (globalCayleyVectorJetBulkClearedSource s hs extent time)
        (globalCayleyVectorJetBulkNorthWeightDeficitSource
          s hs extent time)) := by
  let pure := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetIdentityScaledPurePolynomial extent
        (timeShiftPlaquette time face))
  let cleared := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetClearedPolynomial extent
        (timeShiftPlaquette time face))
  let deficit := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetNorthWeightDeficitPolynomial extent
        (timeShiftPlaquette time face))
  have hpoint : ∀ face, face ∈ bulkSourceFaces s →
      HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
        (pure face) (polyAdd (cleared face) (deficit face)) := by
    intro face _
    have hsplit :=
      globalCayleyVectorJetIdentityScaledPure_carrier_cleared_deficit
        extent (timeShiftPlaquette time face)
    have hscaled := HaarCarrierEqv.smul
      (bulkSourceCoefficient s hs face) hsplit
    exact hscaled.trans (RatPolyCoeffEqv.haarCarrier
      (RatPolyCoeffEqv.smul_add (bulkSourceCoefficient s hs face)
        (globalCayleyVectorJetClearedPolynomial extent
          (timeShiftPlaquette time face))
        (globalCayleyVectorJetNorthWeightDeficitPolynomial extent
          (timeShiftPlaquette time face))))
  have hsum := finiteSum_carrier
    (boundaryCompleteSlabLinks extent).length pure
      (fun face => polyAdd (cleared face) (deficit face))
      (bulkSourceFaces s) hpoint
  have hseparate := finitePolySum_add cleared deficit (bulkSourceFaces s)
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (finitePolySum pure (bulkSourceFaces s))
    (polyAdd
      (finitePolySum cleared (bulkSourceFaces s))
      (finitePolySum deficit (bulkSourceFaces s)))
  exact hsum.trans (RatPolyCoeffEqv.haarCarrier hseparate)

/-- Product of two identity-scaled pure bulk sources. -/
def globalCayleyVectorJetBulkPairIdentityScaledPureSource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  polyMul
    (globalCayleyVectorJetBulkIdentityScaledPureSource
      s hs extent leftTime)
    (globalCayleyVectorJetBulkIdentityScaledPureSource
      s hs extent rightTime)

/-- The three pair-source products containing at least one exact north-weight
deficit. -/
def globalCayleyVectorJetBulkPairNorthWeightDeficitSource
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) : RatPoly :=
  let leftCleared := globalCayleyVectorJetBulkClearedSource
    s hs extent leftTime
  let rightCleared := globalCayleyVectorJetBulkClearedSource
    s hs extent rightTime
  let leftDeficit := globalCayleyVectorJetBulkNorthWeightDeficitSource
    s hs extent leftTime
  let rightDeficit := globalCayleyVectorJetBulkNorthWeightDeficitSource
    s hs extent rightTime
  polyAdd
    (polyMul leftCleared rightDeficit)
    (polyAdd
      (polyMul leftDeficit rightCleared)
      (polyMul leftDeficit rightDeficit))

private theorem product_split_coeff
    (leftCleared leftDeficit rightCleared rightDeficit : RatPoly) :
    RatPolyCoeffEqv
      (polyMul
        (polyAdd leftCleared leftDeficit)
        (polyAdd rightCleared rightDeficit))
      (polyAdd
        (polyMul leftCleared rightCleared)
        (polyAdd
          (polyMul leftCleared rightDeficit)
          (polyAdd
            (polyMul leftDeficit rightCleared)
            (polyMul leftDeficit rightDeficit)))) := by
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add
      (.mul (.var 0) (.var 2))
      (.add
        (.mul (.var 0) (.var 3))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 3)))))
    (by decide)
    (fun
      | 0 => leftCleared
      | 1 => leftDeficit
      | 2 => rightCleared
      | _ => rightDeficit)

/-- The pure pair source is the actual cleared pair plus exactly the three
products carrying at least one `1 - P^14` deficit. -/
theorem globalCayleyVectorJetBulkPairIdentityScaledPure_carrier_cleared_deficit
    (s : Nat) (hs : 0 < s) (extent leftTime rightTime : Nat) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkPairIdentityScaledPureSource
        s hs extent leftTime rightTime)
      (polyAdd
        (globalCayleyVectorJetBulkPairClearedSource
          s hs extent leftTime rightTime)
        (globalCayleyVectorJetBulkPairNorthWeightDeficitSource
          s hs extent leftTime rightTime)) := by
  let leftCleared := globalCayleyVectorJetBulkClearedSource
    s hs extent leftTime
  let rightCleared := globalCayleyVectorJetBulkClearedSource
    s hs extent rightTime
  let leftDeficit := globalCayleyVectorJetBulkNorthWeightDeficitSource
    s hs extent leftTime
  let rightDeficit := globalCayleyVectorJetBulkNorthWeightDeficitSource
    s hs extent rightTime
  have hleft :=
    globalCayleyVectorJetBulkIdentityScaledPure_carrier_cleared_deficit
      s hs extent leftTime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkIdentityScaledPureSource
      s hs extent leftTime)
    (polyAdd leftCleared leftDeficit) at hleft
  have hright :=
    globalCayleyVectorJetBulkIdentityScaledPure_carrier_cleared_deficit
      s hs extent rightTime
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkIdentityScaledPureSource
      s hs extent rightTime)
    (polyAdd rightCleared rightDeficit) at hright
  have hproduct := HaarCarrierEqv.mul hleft hright
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetBulkPairIdentityScaledPureSource
      s hs extent leftTime rightTime)
    (polyMul (polyAdd leftCleared leftDeficit)
      (polyAdd rightCleared rightDeficit)) at hproduct
  exact hproduct.trans (RatPolyCoeffEqv.haarCarrier
    (product_split_coeff leftCleared leftDeficit
      rightCleared rightDeficit))

/-- Normalized ORIGINAL expectation of one identity-scaled pure bulk source. -/
def globalCayleyVectorJetBulkIdentityScaledPureExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkIdentityScaledPureSource
      s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of the exact `1 - P^14` bulk deficit. -/
def globalCayleyVectorJetBulkNorthWeightDeficitExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkNorthWeightDeficitSource
      s hs (centralExtent half) time)

/-- Normalized ORIGINAL expectation of the identity-scaled pure pair. -/
def globalCayleyVectorJetBulkPairIdentityScaledPureExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairIdentityScaledPureSource
      s hs (centralExtent half) leftTime rightTime)

/-- Normalized ORIGINAL expectation of the three pair terms containing a
north-weight deficit. -/
def globalCayleyVectorJetBulkPairNorthWeightDeficitExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetBulkPairNorthWeightDeficitSource
      s hs (centralExtent half) leftTime rightTime)

/-- The one-source exact north-weight split passes through the unchanged
normalized ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkIdentityScaledPureExpectation_cleared_deficit
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (time : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkIdentityScaledPureExpectation
        w hw0 hw1 half s hs time)
      (CReal.add
        (globalCayleyVectorJetBulkClearedExpectation
          w hw0 hw1 half s hs time)
        (globalCayleyVectorJetBulkNorthWeightDeficitExpectation
          w hw0 hw1 half s hs time)) := by
  let pure := globalCayleyVectorJetBulkIdentityScaledPureSource
    s hs (centralExtent half) time
  let cleared := globalCayleyVectorJetBulkClearedSource
    s hs (centralExtent half) time
  let deficit := globalCayleyVectorJetBulkNorthWeightDeficitSource
    s hs (centralExtent half) time
  have hcarrier :=
    globalCayleyVectorJetBulkIdentityScaledPure_carrier_cleared_deficit
      s hs (centralExtent half) time
  have hcongr := BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half hcarrier
  change CReal.Equiv
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half pure)
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
      (polyAdd cleared deficit)) at hcongr
  exact hcongr.trans
    (BF4ExactSlabPolynomialExpectation.expectation_add
      w hw0 hw1 half cleared deficit)

/-- The pair exact north-weight split passes through the same normalized
ORIGINAL expectation. -/
theorem globalCayleyVectorJetBulkPairIdentityScaledPureExpectation_cleared_deficit
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkPairIdentityScaledPureExpectation
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkPairClearedExpectation
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkPairNorthWeightDeficitExpectation
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let purePair := globalCayleyVectorJetBulkPairIdentityScaledPureSource
    s hs (centralExtent half) leftTime rightTime
  let clearedPair := globalCayleyVectorJetBulkPairClearedSource
    s hs (centralExtent half) leftTime rightTime
  let deficitPair := globalCayleyVectorJetBulkPairNorthWeightDeficitSource
    s hs (centralExtent half) leftTime rightTime
  have hcarrier :=
    globalCayleyVectorJetBulkPairIdentityScaledPure_carrier_cleared_deficit
      s hs (centralExtent half) leftTime rightTime
  have hcongr := BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half hcarrier
  change CReal.Equiv
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half purePair)
    (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
      (polyAdd clearedPair deficitPair)) at hcongr
  exact hcongr.trans
    (BF4ExactSlabPolynomialExpectation.expectation_add
      w hw0 hw1 half clearedPair deficitPair)

/-- Centered normalized ORIGINAL response of the two identity-scaled pure
bulk vector-jet sources. -/
def globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  CReal.sub
    (globalCayleyVectorJetBulkPairIdentityScaledPureExpectation
      w hw0 hw1 half s hs leftTime rightTime)
    (CReal.mul
      (globalCayleyVectorJetBulkIdentityScaledPureExpectation
        w hw0 hw1 half s hs leftTime)
      (globalCayleyVectorJetBulkIdentityScaledPureExpectation
        w hw0 hw1 half s hs rightTime))

/-- Exact centered correction.  Every term contains at least one source with
the literal facewise factor `1 - P^14`, and both one-source centers remain
under the same ORIGINAL normalization. -/
def globalCayleyVectorJetBulkCenteredNorthWeightDeficit
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) : CReal :=
  let leftCleared := globalCayleyVectorJetBulkClearedExpectation
    w hw0 hw1 half s hs leftTime
  let rightCleared := globalCayleyVectorJetBulkClearedExpectation
    w hw0 hw1 half s hs rightTime
  let leftDeficit := globalCayleyVectorJetBulkNorthWeightDeficitExpectation
    w hw0 hw1 half s hs leftTime
  let rightDeficit := globalCayleyVectorJetBulkNorthWeightDeficitExpectation
    w hw0 hw1 half s hs rightTime
  let pairDeficit := globalCayleyVectorJetBulkPairNorthWeightDeficitExpectation
    w hw0 hw1 half s hs leftTime rightTime
  CReal.sub pairDeficit
    (CReal.add
      (CReal.mul leftCleared rightDeficit)
      (CReal.add
        (CReal.mul leftDeficit rightCleared)
        (CReal.mul leftDeficit rightDeficit)))

private theorem centeredSplitQ
    (clearedPair pairDeficit leftCleared leftDeficit
      rightCleared rightDeficit : Q') :
    (clearedPair + pairDeficit) +
        -((leftCleared + leftDeficit) *
          (rightCleared + rightDeficit)) ≈
      (clearedPair + -(leftCleared * rightCleared)) +
        (pairDeficit +
          -(leftCleared * rightDeficit +
            (leftDeficit * rightCleared +
              leftDeficit * rightDeficit))) := by
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
      | 0 => clearedPair
      | 1 => pairDeficit
      | 2 => leftCleared
      | 3 => leftDeficit
      | 4 => rightCleared
      | _ => rightDeficit)

/-- Exact centered comparison under one unchanged normalized ORIGINAL action:
the identity-scaled pure response is the actual cleared response plus a
correction in which every source term contains `1 - P^14`. -/
theorem globalCayleyVectorJetBulkCenteredIdentityScaledPure_cleared_deficit
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half s : Nat) (hs : 0 < s) (leftTime rightTime : Nat) :
    CReal.Equiv
      (globalCayleyVectorJetBulkCenteredIdentityScaledPureResponse
        w hw0 hw1 half s hs leftTime rightTime)
      (CReal.add
        (globalCayleyVectorJetBulkCenteredClearedResponse
          w hw0 hw1 half s hs leftTime rightTime)
        (globalCayleyVectorJetBulkCenteredNorthWeightDeficit
          w hw0 hw1 half s hs leftTime rightTime)) := by
  let purePair := globalCayleyVectorJetBulkPairIdentityScaledPureExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let clearedPair := globalCayleyVectorJetBulkPairClearedExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let pairDeficit := globalCayleyVectorJetBulkPairNorthWeightDeficitExpectation
    w hw0 hw1 half s hs leftTime rightTime
  let leftPure := globalCayleyVectorJetBulkIdentityScaledPureExpectation
    w hw0 hw1 half s hs leftTime
  let rightPure := globalCayleyVectorJetBulkIdentityScaledPureExpectation
    w hw0 hw1 half s hs rightTime
  let leftCleared := globalCayleyVectorJetBulkClearedExpectation
    w hw0 hw1 half s hs leftTime
  let rightCleared := globalCayleyVectorJetBulkClearedExpectation
    w hw0 hw1 half s hs rightTime
  let leftDeficit := globalCayleyVectorJetBulkNorthWeightDeficitExpectation
    w hw0 hw1 half s hs leftTime
  let rightDeficit := globalCayleyVectorJetBulkNorthWeightDeficitExpectation
    w hw0 hw1 half s hs rightTime
  have hpair :=
    globalCayleyVectorJetBulkPairIdentityScaledPureExpectation_cleared_deficit
      w hw0 hw1 half s hs leftTime rightTime
  change CReal.Equiv purePair
    (CReal.add clearedPair pairDeficit) at hpair
  have hleft :=
    globalCayleyVectorJetBulkIdentityScaledPureExpectation_cleared_deficit
      w hw0 hw1 half s hs leftTime
  change CReal.Equiv leftPure
    (CReal.add leftCleared leftDeficit) at hleft
  have hright :=
    globalCayleyVectorJetBulkIdentityScaledPureExpectation_cleared_deficit
      w hw0 hw1 half s hs rightTime
  change CReal.Equiv rightPure
    (CReal.add rightCleared rightDeficit) at hright
  have hmeans : CReal.Equiv
      (CReal.mul leftPure rightPure)
      (CReal.mul
        (CReal.add leftCleared leftDeficit)
        (CReal.add rightCleared rightDeficit)) :=
    Pivot2.mul_congr hleft hright
  have hsub : CReal.Equiv
      (CReal.sub purePair (CReal.mul leftPure rightPure))
      (CReal.sub
        (CReal.add clearedPair pairDeficit)
        (CReal.mul
          (CReal.add leftCleared leftDeficit)
          (CReal.add rightCleared rightDeficit))) :=
    (CReal.sub_congr_left hpair).trans (CReal.sub_congr_right hmeans)
  have hregroup : CReal.Equiv
      (CReal.sub
        (CReal.add clearedPair pairDeficit)
        (CReal.mul
          (CReal.add leftCleared leftDeficit)
          (CReal.add rightCleared rightDeficit)))
      (CReal.add
        (CReal.sub clearedPair
          (CReal.mul leftCleared rightCleared))
        (CReal.sub pairDeficit
          (CReal.add
            (CReal.mul leftCleared rightDeficit)
            (CReal.add
              (CReal.mul leftDeficit rightCleared)
              (CReal.mul leftDeficit rightDeficit))))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      centeredSplitQ
        (clearedPair.approx n) (pairDeficit.approx n)
        (leftCleared.approx n) (leftDeficit.approx n)
        (rightCleared.approx n) (rightDeficit.approx n))
  change CReal.Equiv
    (CReal.sub purePair (CReal.mul leftPure rightPure)) _
  exact hsub.trans hregroup

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit.globalCayleyVectorJetNorthWeightScale_eq_identity
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit.globalCayleyVectorJetIdentityScaledPure_carrier_cleared_deficit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit.globalCayleyVectorJetBulkIdentityScaledPure_carrier_cleared_deficit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit.globalCayleyVectorJetBulkPairIdentityScaledPure_carrier_cleared_deficit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit.globalCayleyVectorJetBulkIdentityScaledPureExpectation_cleared_deficit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit.globalCayleyVectorJetBulkPairIdentityScaledPureExpectation_cleared_deficit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit.globalCayleyVectorJetBulkCenteredIdentityScaledPure_cleared_deficit
