/-
# Global ORIGINAL-carrier Cayley split for the plaquette vector jet

The pointwise Cayley vector-jet identity is lifted to the literal finite
`RatPoly` carrier of one corrected-slab plaquette.  The global common
denominator is retained.  The resulting equality is valid after every later
Haar insertion and therefore passes directly to the normalized ORIGINAL
expectation.

No denominator inversion, residual estimate, FREE Gaussian comparison,
cutoff removal, continuum theory, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet

set_option autoImplicit false
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

/-- The three-coordinate vector norm of the literal corrected-slab
plaquette polynomial. -/
def globalPlaquetteVectorJet (extent : Nat) (face : Z4Plaq) : RatPoly :=
  let q := correctedSlabPlaquettePolynomial extent face
  polyAdd (polyMul q.iPart q.iPart)
    (polyAdd (polyMul q.jPart q.jPart) (polyMul q.kPart q.kPart))

/-- The complete degree-three-through-six part of the global cleared Cayley
deficit. -/
def globalCayleyHigherPolynomial (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyAdd
    (polyAdd
      (globalCayleyDegreeThreePolynomial extent face)
      (globalCayleyDegreeFourPolynomial extent face))
    (polyAdd
      (globalCayleyDegreeFivePolynomial extent face)
      (globalCayleyDegreeSixPolynomial extent face))

/-- The denominator-square-cleared ORIGINAL vector-jet observable. -/
def globalCayleyVectorJetClearedPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  let denominator := globalCayleyDenominatorPolynomial extent face
  polyMul
    (polyMul (polyConst 4) (polyMul denominator denominator))
    (globalPlaquetteVectorJet extent face)

/-- Residual after extracting the degree-two Cayley polynomial from the
denominator-square-cleared vector jet. -/
def globalCayleyVectorJetRemainderPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  let denominator := globalCayleyDenominatorPolynomial extent face
  let deficit := globalCayleyDeficitPolynomial extent face
  polyAdd
    (polyMul (polyMul (polyConst 4) denominator)
      (globalCayleyHigherPolynomial extent face))
    (polyNeg (polyMul deficit deficit))

/-- Unit radius identifies the vector jet with the complement of the scalar
square on the full corrected-slab Haar carrier. -/
theorem globalPlaquetteVectorJet_scalar_complement
    {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalPlaquetteVectorJet extent face)
      (polyAdd polyOne
        (polyNeg
          (polyMul (correctedSlabPlaquettePolynomial extent face).scalar
            (correctedSlabPlaquettePolynomial extent face).scalar))) := by
  let q := correctedSlabPlaquettePolynomial extent face
  let scalarSquare := polyMul q.scalar q.scalar
  let vectorJet := globalPlaquetteVectorJet extent face
  have hnorm : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm q) polyOne :=
    haarNorm_slabPlaquette hface
  have hreplace : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyAdd polyOne (polyNeg scalarSquare))
      (polyAdd (polyQuaternionNorm q) (polyNeg scalarSquare)) :=
    HaarCarrierEqv.add hnorm.symm (HaarCarrierEqv.refl _ _)
  have hcancel : RatPolyCoeffEqv
      (polyAdd (polyQuaternionNorm q) (polyNeg scalarSquare)) vectorJet := by
    dsimp only [vectorJet, scalarSquare, q, globalPlaquetteVectorJet,
      polyQuaternionNorm]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.mul (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 1))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
        (.neg (.mul (.var 0) (.var 0))))
      (.add (.mul (.var 1) (.var 1))
        (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))
      (by decide)
      (fun
        | 0 => (correctedSlabPlaquettePolynomial extent face).scalar
        | 1 => (correctedSlabPlaquettePolynomial extent face).iPart
        | 2 => (correctedSlabPlaquettePolynomial extent face).jPart
        | _ => (correctedSlabPlaquettePolynomial extent face).kPart)
  exact (hreplace.trans (RatPolyCoeffEqv.haarCarrier hcancel)).symm

private theorem globalCayleyLeftPolynomial_coeff_denominator_delta
    (extent : Nat) (face : Z4Plaq) :
    let denominator := globalCayleyDenominatorPolynomial extent face
    let scalar := (correctedSlabPlaquettePolynomial extent face).scalar
    RatPolyCoeffEqv (globalCayleyLeftPolynomial extent face)
      (polyMul denominator
        (polyAdd (polyConst 2)
          (polyNeg (polyMul (polyConst 2) scalar)))) := by
  dsimp only
  let denominator := globalCayleyDenominatorPolynomial extent face
  let scalar := (correctedSlabPlaquettePolynomial extent face).scalar
  have hexpanded := globalCayleyLeftPolynomial_coeff_original extent face
  have hfactor : RatPolyCoeffEqv
      (polyAdd
        (polyMul (polyConst 2) denominator)
        (polyNeg
          (polyMul (polyConst 2) (polyMul denominator scalar))))
      (polyMul denominator
        (polyAdd (polyConst 2)
          (polyNeg (polyMul (polyConst 2) scalar)))) := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (2 * .var 0 + -(2 * (.var 0 * .var 1)))
      (.var 0 * (2 + -(2 * .var 1)))
      (by decide)
      (fun | 0 => denominator | _ => scalar)
  exact hexpanded.trans hfactor

/-- The denominator-square-cleared vector jet is exactly four times the
denominator times the cleared deficit minus the cleared deficit square. -/
theorem globalCayleyVectorJet_cleared_carrier
    {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    let denominator := globalCayleyDenominatorPolynomial extent face
    let deficit := globalCayleyDeficitPolynomial extent face
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetClearedPolynomial extent face)
      (polyAdd
        (polyMul (polyMul (polyConst 4) denominator) deficit)
        (polyNeg (polyMul deficit deficit))) := by
  dsimp only
  let blocks := (boundaryCompleteSlabLinks extent).length
  let denominator := globalCayleyDenominatorPolynomial extent face
  let deficit := globalCayleyDeficitPolynomial extent face
  let left := globalCayleyLeftPolynomial extent face
  let scalar := (correctedSlabPlaquettePolynomial extent face).scalar
  let scalarProxy := polyAdd polyOne (polyNeg (polyMul scalar scalar))
  let delta := polyAdd (polyConst 2)
    (polyNeg (polyMul (polyConst 2) scalar))
  let denominatorDelta := polyMul denominator delta
  let fourDenominator := polyMul (polyConst 4) denominator
  let clearedFactor := polyMul (polyConst 4)
    (polyMul denominator denominator)
  have hjet := globalPlaquetteVectorJet_scalar_complement hface
  change HaarCarrierEqv blocks (globalPlaquetteVectorJet extent face)
    scalarProxy at hjet
  have hleft : HaarCarrierEqv blocks
      (globalCayleyVectorJetClearedPolynomial extent face)
      (polyMul clearedFactor scalarProxy) := by
    unfold globalCayleyVectorJetClearedPolynomial clearedFactor denominator
    exact HaarCarrierEqv.mul_left _ hjet
  have hcore : RatPolyCoeffEqv
      (polyMul clearedFactor scalarProxy)
      (polyAdd
        (polyMul fourDenominator denominatorDelta)
        (polyNeg (polyMul denominatorDelta denominatorDelta))) := by
    unfold clearedFactor fourDenominator denominatorDelta delta scalarProxy
    exact coeffEvalExpr_eqv_of_normalize_eq
      ((4 * (.var 0 * .var 0)) * (1 + -(.var 1 * .var 1)))
      ((4 * .var 0) * (.var 0 * (2 + -(2 * .var 1))) +
        -((.var 0 * (2 + -(2 * .var 1))) *
          (.var 0 * (2 + -(2 * .var 1)))))
      (by decide)
      (fun | 0 => denominator | _ => scalar)
  have hleftShape := globalCayleyLeftPolynomial_coeff_denominator_delta
    extent face
  change RatPolyCoeffEqv left denominatorDelta at hleftShape
  have hreplace : RatPolyCoeffEqv
      (polyAdd
        (polyMul fourDenominator denominatorDelta)
        (polyNeg (polyMul denominatorDelta denominatorDelta)))
      (polyAdd
        (polyMul fourDenominator left)
        (polyNeg (polyMul left left))) :=
    (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) hleftShape.symm).add
      (RatPolyCoeffEqv.neg
        (RatPolyCoeffEqv.mul hleftShape.symm hleftShape.symm))
  have hdeficit : HaarCarrierEqv blocks left deficit := by
    exact globalCayleyPolynomial_carrier extent face
  have hdeficitReplace : HaarCarrierEqv blocks
      (polyAdd
        (polyMul fourDenominator left)
        (polyNeg (polyMul left left)))
      (polyAdd
        (polyMul fourDenominator deficit)
        (polyNeg (polyMul deficit deficit))) :=
    HaarCarrierEqv.add
      (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) hdeficit)
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul hdeficit hdeficit))
  exact hleft.trans
    ((RatPolyCoeffEqv.haarCarrier (hcore.trans hreplace)).trans
      hdeficitReplace)

/-- The global cleared deficit is its degree-two term plus the complete
degree-three-through-six polynomial. -/
theorem globalCayleyDeficitPolynomial_coeff_quadratic_higher
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (globalCayleyDeficitPolynomial extent face)
      (polyAdd
        (globalCayleyDegreeTwoPolynomial extent face)
        (globalCayleyHigherPolynomial extent face)) := by
  have hdegrees := globalCayleyDeficitPolynomial_coeff_degrees extent face
  let p2 := globalCayleyDegreeTwoPolynomial extent face
  let p3 := globalCayleyDegreeThreePolynomial extent face
  let p4 := globalCayleyDegreeFourPolynomial extent face
  let p5 := globalCayleyDegreeFivePolynomial extent face
  let p6 := globalCayleyDegreeSixPolynomial extent face
  have hregroup : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyAdd (polyAdd p2 p3) p4) p5) p6)
      (polyAdd p2 (globalCayleyHigherPolynomial extent face)) := by
    unfold globalCayleyHigherPolynomial
    exact coeffEvalExpr_eqv_of_normalize_eq
      (((.var 0 + .var 1) + .var 2) + .var 3 + .var 4)
      (.var 0 + ((.var 1 + .var 2) + (.var 3 + .var 4)))
      (by decide)
      (fun | 0 => p2 | 1 => p3 | 2 => p4 | 3 => p5 | _ => p6)
  exact hdegrees.trans hregroup

/-- The ORIGINAL carrier identity with the literal degree-two Cayley
polynomial separated from one explicit global residual. -/
theorem globalCayleyVectorJet_quadratic_remainder_carrier
    {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    let denominator := globalCayleyDenominatorPolynomial extent face
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetClearedPolynomial extent face)
      (polyAdd
        (polyMul (polyMul (polyConst 4) denominator)
          (globalCayleyDegreeTwoPolynomial extent face))
        (globalCayleyVectorJetRemainderPolynomial extent face)) := by
  dsimp only
  let blocks := (boundaryCompleteSlabLinks extent).length
  let denominator := globalCayleyDenominatorPolynomial extent face
  let deficit := globalCayleyDeficitPolynomial extent face
  let quadratic := globalCayleyDegreeTwoPolynomial extent face
  let higher := globalCayleyHigherPolynomial extent face
  let fourDenominator := polyMul (polyConst 4) denominator
  have hbase := globalCayleyVectorJet_cleared_carrier hface
  change HaarCarrierEqv blocks
    (globalCayleyVectorJetClearedPolynomial extent face)
    (polyAdd (polyMul fourDenominator deficit)
      (polyNeg (polyMul deficit deficit))) at hbase
  have hsplit := globalCayleyDeficitPolynomial_coeff_quadratic_higher
    extent face
  change RatPolyCoeffEqv deficit (polyAdd quadratic higher) at hsplit
  have hreplace : RatPolyCoeffEqv
      (polyAdd (polyMul fourDenominator deficit)
        (polyNeg (polyMul deficit deficit)))
      (polyAdd (polyMul fourDenominator (polyAdd quadratic higher))
        (polyNeg (polyMul deficit deficit))) :=
    (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl _) hsplit).add
      (RatPolyCoeffEqv.refl _)
  have hregroup : RatPolyCoeffEqv
      (polyAdd (polyMul fourDenominator (polyAdd quadratic higher))
        (polyNeg (polyMul deficit deficit)))
      (polyAdd (polyMul fourDenominator quadratic)
        (polyAdd (polyMul fourDenominator higher)
          (polyNeg (polyMul deficit deficit)))) := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.var 0 * (.var 1 + .var 2) + -(.var 3 * .var 3))
      (.var 0 * .var 1 +
        (.var 0 * .var 2 + -(.var 3 * .var 3)))
      (by decide)
      (fun | 0 => fourDenominator | 1 => quadratic | 2 => higher | _ => deficit)
  unfold globalCayleyVectorJetRemainderPolynomial
  exact hbase.trans (RatPolyCoeffEqv.haarCarrier (hreplace.trans hregroup))

/-- Normalized ORIGINAL expectation of the cleared vector jet. -/
def globalCayleyVectorJetClearedExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetClearedPolynomial (centralExtent half) face)

/-- Normalized ORIGINAL expectation of the extracted Cayley quadratic term. -/
def globalCayleyVectorJetQuadraticExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  let extent := centralExtent half
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (polyMul
      (polyMul (polyConst 4)
        (globalCayleyDenominatorPolynomial extent face))
      (globalCayleyDegreeTwoPolynomial extent face))

/-- Normalized ORIGINAL expectation of the exact global vector-jet residual. -/
def globalCayleyVectorJetRemainderExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetRemainderPolynomial (centralExtent half) face)

/-- The exact carrier split passes to the normalized ORIGINAL expectation
without changing the action or partition function. -/
theorem globalCayleyVectorJet_originalExpectation_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq)
    (hface : face ∈ boundaryCompleteSlabPlaquettes (centralExtent half)) :
    CReal.Equiv
      (globalCayleyVectorJetClearedExpectation w hw0 hw1 half face)
      (CReal.add
        (globalCayleyVectorJetQuadraticExpectation w hw0 hw1 half face)
        (globalCayleyVectorJetRemainderExpectation w hw0 hw1 half face)) := by
  let extent := centralExtent half
  let denominator := globalCayleyDenominatorPolynomial extent face
  let quadratic := globalCayleyDegreeTwoPolynomial extent face
  let remainder := globalCayleyVectorJetRemainderPolynomial extent face
  have hcarrier := globalCayleyVectorJet_quadratic_remainder_carrier hface
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetClearedPolynomial extent face)
    (polyAdd (polyMul (polyMul (polyConst 4) denominator) quadratic)
      remainder) at hcarrier
  have hcongr := BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half hcarrier
  exact hcongr.trans (by
    simpa [globalCayleyVectorJetClearedExpectation,
      globalCayleyVectorJetQuadraticExpectation,
      globalCayleyVectorJetRemainderExpectation, extent, denominator,
      quadratic, remainder] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half
            (polyMul (polyMul (polyConst 4) denominator) quadratic)
            remainder)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet.globalPlaquetteVectorJet_scalar_complement
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet.globalCayleyVectorJet_cleared_carrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet.globalCayleyDeficitPolynomial_coeff_quadratic_higher
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet.globalCayleyVectorJet_quadratic_remainder_carrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet.globalCayleyVectorJet_originalExpectation_split
