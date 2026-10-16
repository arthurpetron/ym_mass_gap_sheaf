/-
# Identity-chart quadratic part of the global Cayley vector jet

The degree-two global Cayley polynomial is first exposed as an explicit
four-oriented-link carrier.  Freezing its common chart denominator at `16`
and its four complementary chart products at `8` gives the exact inner scale

  `16^6 * 4 * 8^2 = 2^32`.

The resulting identity-chart curl square is split from the complete inner
degree-two polynomial, and the correction retains every scalar-dependent
denominator factor.  The split is then inserted into the canonical outer
reference term from the preceding identity-denominator result.

This is exact finite carrier algebra only.  It does not identify ORIGINAL and
FREE laws, bound either denominator remainder, remove a cutoff, construct a
continuum theory, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityDenominator

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetPair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkOuterDenominator
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityDenominator
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QuaternionHaarGammaFiniteSum
  (finitePolySum_add)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev PE := PolyExpr
local infix:50 " ≈ " => Q'.eqv
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

/-- The first oriented link in the plaquette word. -/
def identityQuadraticFaceEntry0 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(face.1, (dirsOf face.2).1), false⟩

/-- The second oriented link in the plaquette word. -/
def identityQuadraticFaceEntry1 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(addE face.1 (dirsOf face.2).1, (dirsOf face.2).2), false⟩

/-- The reversed third link in the plaquette word. -/
def identityQuadraticFaceEntry2 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(addE face.1 (dirsOf face.2).2, (dirsOf face.2).1), true⟩

/-- The reversed fourth link in the plaquette word. -/
def identityQuadraticFaceEntry3 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(face.1, (dirsOf face.2).2), true⟩

/-- Explicit global `D^6 H₂` carrier for four polynomial quaternions. -/
def compiledCayleyDegreeTwoPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  let d0 := cayleyChartDenominatorPolynomial q0
  let d1 := cayleyChartDenominatorPolynomial q1
  let d2 := cayleyChartDenominatorPolynomial q2
  let d3 := cayleyChartDenominatorPolynomial q3
  let denominator := polyMul (polyMul (polyMul d0 d1) d2) d3
  let complement0 := cayleyComplement0Polynomial q0 q1 q2 q3
  let complement1 := cayleyComplement1Polynomial q0 q1 q2 q3
  let complement2 := cayleyComplement2Polynomial q0 q1 q2 q3
  let complement3 := cayleyComplement3Polynomial q0 q1 q2 q3
  let iCurl := polyAdd
    (polyAdd
      (polyAdd
        (polyMul complement0 q0.iPart)
        (polyMul complement1 q1.iPart))
      (polyMul complement2 q2.iPart))
    (polyMul complement3 q3.iPart)
  let jCurl := polyAdd
    (polyAdd
      (polyAdd
        (polyMul complement0 q0.jPart)
        (polyMul complement1 q1.jPart))
      (polyMul complement2 q2.jPart))
    (polyMul complement3 q3.jPart)
  let kCurl := polyAdd
    (polyAdd
      (polyAdd
        (polyMul complement0 q0.kPart)
        (polyMul complement1 q1.kPart))
      (polyMul complement2 q2.kPart))
    (polyMul complement3 q3.kPart)
  let curlNorm := polyAdd
    (polyAdd (polyMul iCurl iCurl) (polyMul jCurl jCurl))
    (polyMul kCurl kCurl)
  let denominatorSquare := polyMul denominator denominator
  let denominatorSixth := polyMul
    (polyMul denominatorSquare denominatorSquare) denominatorSquare
  polyMul denominatorSixth (polyMul (polyConst 4) curlNorm)

/-- The private expression-generated degree-two face polynomial is
coefficientwise the displayed four-link `D^6 H₂` carrier. -/
theorem globalCayleyDegreeTwoPolynomial_coeff_compiled
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleyDegreeTwoPolynomial extent face)
      (compiledCayleyDegreeTwoPolynomial
        (orientedCorrectedSlabLinkPolynomial extent
          (identityQuadraticFaceEntry0 face))
        (orientedCorrectedSlabLinkPolynomial extent
          (identityQuadraticFaceEntry1 face))
        (orientedCorrectedSlabLinkPolynomial extent
          (identityQuadraticFaceEntry2 face))
        (orientedCorrectedSlabLinkPolynomial extent
          (identityQuadraticFaceEntry3 face))) := by
  exact RatPolyCoeffEqv.refl _

/-- Unscaled squared oriented imaginary curl of four polynomial
quaternions. -/
def cayleyIdentityCurlNormPolynomial
    (q0 q1 q2 q3 : PolyQuaternion) : RatPoly :=
  let iCurl := polyAdd
    (polyAdd (polyAdd q0.iPart q1.iPart) q2.iPart) q3.iPart
  let jCurl := polyAdd
    (polyAdd (polyAdd q0.jPart q1.jPart) q2.jPart) q3.jPart
  let kCurl := polyAdd
    (polyAdd (polyAdd q0.kPart q1.kPart) q2.kPart) q3.kPart
  polyAdd
    (polyAdd (polyMul iCurl iCurl) (polyMul jCurl jCurl))
    (polyMul kCurl kCurl)

/-- Scale obtained by freezing `D=16` and every complementary chart product
at `8` in `D^6 H₂`. -/
def identityCayleyInnerQuadraticScale : Q' :=
  (((16 * 16) * (16 * 16)) * (16 * 16)) * (4 * (8 * 8))

/-- The frozen inner scale is the same exact `2^32` rational that appears as
the identity value of the outer global clearing denominator. -/
theorem identityCayleyInnerQuadraticScale_eq_reference :
    identityCayleyInnerQuadraticScale ≈
      identityCayleyDenominatorReference := by
  decide

/-- The identity-chart quadratic part of the inner degree-two polynomial for
one ORIGINAL oriented face. -/
def globalCayleyIdentityInnerQuadraticPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul (polyConst identityCayleyInnerQuadraticScale)
    (cayleyIdentityCurlNormPolynomial
      (orientedCorrectedSlabLinkPolynomial extent
        (identityQuadraticFaceEntry0 face))
      (orientedCorrectedSlabLinkPolynomial extent
        (identityQuadraticFaceEntry1 face))
      (orientedCorrectedSlabLinkPolynomial extent
        (identityQuadraticFaceEntry2 face))
      (orientedCorrectedSlabLinkPolynomial extent
        (identityQuadraticFaceEntry3 face)))

/-- Every inner chart-denominator correction, with no term discarded. -/
def globalCayleyInnerDenominatorRemainderPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyAdd
    (globalCayleyDegreeTwoPolynomial extent face)
    (polyNeg (globalCayleyIdentityInnerQuadraticPolynomial extent face))

private theorem inner_split_coeff
    (complete identityPart : RatPoly) :
    RatPolyCoeffEqv complete
      (polyAdd identityPart
        (polyAdd complete (polyNeg identityPart))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.var 0)
    (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
    (by decide)
    (fun
      | 0 => complete
      | _ => identityPart)

/-- Exact split of the complete inner `P₂` polynomial into its identity-chart
quadratic part and all remaining denominator-dependent terms. -/
theorem globalCayleyDegreeTwoPolynomial_identity_inner_split
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleyDegreeTwoPolynomial extent face)
      (polyAdd
        (globalCayleyIdentityInnerQuadraticPolynomial extent face)
        (globalCayleyInnerDenominatorRemainderPolynomial extent face)) := by
  simpa [globalCayleyInnerDenominatorRemainderPolynomial] using
    inner_split_coeff
      (globalCayleyDegreeTwoPolynomial extent face)
      (globalCayleyIdentityInnerQuadraticPolynomial extent face)

/-- Fully identity-normalized one-face quadratic vector-jet carrier.  Its
outer and inner identity factors are both retained explicitly. -/
def globalCayleyVectorJetIdentityQuadraticPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polyMul (polyConst 4)
      (polyConst identityCayleyDenominatorReference))
    (globalCayleyIdentityInnerQuadraticPolynomial extent face)

/-- Exact correction left inside the canonical outer-reference term after
freezing the inner degree-two chart factors. -/
def globalCayleyVectorJetInnerDenominatorRemainderPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polyMul (polyConst 4)
      (polyConst identityCayleyDenominatorReference))
    (globalCayleyInnerDenominatorRemainderPolynomial extent face)

/-- The canonical outer-reference quadratic term splits exactly into the
fully identity-normalized curl square and the complete inner-denominator
remainder. -/
theorem globalCayleyVectorJetReferenceQuadratic_identity_inner_split
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleyVectorJetReferenceQuadraticPolynomial
        identityCayleyDenominatorReference extent face)
      (polyAdd
        (globalCayleyVectorJetIdentityQuadraticPolynomial extent face)
        (globalCayleyVectorJetInnerDenominatorRemainderPolynomial
          extent face)) := by
  let scalePolynomial := polyMul (polyConst 4)
    (polyConst identityCayleyDenominatorReference)
  have hinner := RatPolyCoeffEqv.mul
    (RatPolyCoeffEqv.refl scalePolynomial)
    (globalCayleyDegreeTwoPolynomial_identity_inner_split extent face)
  exact hinner.trans
    (RatPolyCoeffEqv.mul_add_right scalePolynomial
      (globalCayleyIdentityInnerQuadraticPolynomial extent face)
      (globalCayleyInnerDenominatorRemainderPolynomial extent face))

/-- Total scalar multiplying the unscaled identity-chart curl square in the
canonical outer-reference vector-jet term. -/
def identityCayleyVectorJetQuadraticScale : Q' :=
  (4 * identityCayleyDenominatorReference) *
    identityCayleyInnerQuadraticScale

/-- The combined outer and inner identity-chart vector-jet scale is exactly
`2^66`. -/
theorem identityCayleyVectorJetQuadraticScale_eq_pow :
    identityCayleyVectorJetQuadraticScale ≈
      Q'.ofNat 73786976294838206464 := by
  decide

/-- Literal weighted fully identity-normalized quadratic source at one
chronological placement. -/
def globalCayleyVectorJetBulkIdentityQuadraticSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetIdentityQuadraticPolynomial extent
        (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

/-- Literal weighted inner-denominator correction source at one chronological
placement. -/
def globalCayleyVectorJetBulkInnerDenominatorRemainderSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetInnerDenominatorRemainderPolynomial extent
        (timeShiftPlaquette time face)))
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

/-- The literal weighted canonical outer-reference source splits exactly into
the fully identity-normalized `2^66` curl-square source and the complete
weighted inner-denominator correction source. -/
theorem globalCayleyVectorJetBulkReferenceQuadratic_identity_inner_split
    (s : Nat) (hs : 0 < s) (extent time : Nat) :
    RatPolyCoeffEqv
      (globalCayleyVectorJetBulkReferenceQuadraticSource
        identityCayleyDenominatorReference s hs extent time)
      (polyAdd
        (globalCayleyVectorJetBulkIdentityQuadraticSource
          s hs extent time)
        (globalCayleyVectorJetBulkInnerDenominatorRemainderSource
          s hs extent time)) := by
  let complete := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetReferenceQuadraticPolynomial
        identityCayleyDenominatorReference extent
          (timeShiftPlaquette time face))
  let identityPart := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetIdentityQuadraticPolynomial extent
        (timeShiftPlaquette time face))
  let remainder := fun face =>
    polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetInnerDenominatorRemainderPolynomial extent
        (timeShiftPlaquette time face))
  have hsum := finiteSum_coeff complete
    (fun face => polyAdd (identityPart face) (remainder face))
    (bulkSourceFaces s) (fun face _ => by
      have hface :=
        (globalCayleyVectorJetReferenceQuadratic_identity_inner_split
          extent (timeShiftPlaquette time face)).smul
            (bulkSourceCoefficient s hs face)
      exact hface.trans
        (RatPolyCoeffEqv.smul_add (bulkSourceCoefficient s hs face)
          (globalCayleyVectorJetIdentityQuadraticPolynomial extent
            (timeShiftPlaquette time face))
          (globalCayleyVectorJetInnerDenominatorRemainderPolynomial extent
            (timeShiftPlaquette time face))))
  have hseparate := finitePolySum_add
    identityPart remainder (bulkSourceFaces s)
  change RatPolyCoeffEqv
    (finitePolySum complete (bulkSourceFaces s))
    (polyAdd
      (finitePolySum identityPart (bulkSourceFaces s))
      (finitePolySum remainder (bulkSourceFaces s)))
  exact hsum.trans hseparate

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic.globalCayleyDegreeTwoPolynomial_coeff_compiled
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic.identityCayleyInnerQuadraticScale_eq_reference
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic.globalCayleyDegreeTwoPolynomial_identity_inner_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic.globalCayleyVectorJetReferenceQuadratic_identity_inner_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic.identityCayleyVectorJetQuadraticScale_eq_pow
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkIdentityQuadratic.globalCayleyVectorJetBulkReferenceQuadratic_identity_inner_split
