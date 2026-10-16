/-
# Exact two-plaquette global Cayley vector-jet split

The one-plaquette cleared vector jet is multiplied for two physical slab
faces.  Exact carrier algebra isolates the degree-two--degree-two product and
groups the other three products into one explicit pair residual.  The split
then passes to the normalized ORIGINAL expectation.

No bound on the pair residual, weighted source sum, centering comparison,
FREE Gaussian comparison, cutoff removal, continuum theory, or mass gap is
asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetPair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

/-- The extracted global degree-two contribution for one cleared vector
jet. -/
def globalCayleyVectorJetQuadraticPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polyMul (polyConst 4)
      (globalCayleyDenominatorPolynomial extent face))
    (globalCayleyDegreeTwoPolynomial extent face)

/-- Product of the two denominator-square-cleared vector jets. -/
def globalCayleyVectorJetPairClearedPolynomial
    (extent : Nat) (left right : Z4Plaq) : RatPoly :=
  polyMul
    (globalCayleyVectorJetClearedPolynomial extent left)
    (globalCayleyVectorJetClearedPolynomial extent right)

/-- The three exact pair terms containing at least one global vector-jet
residual. -/
def globalCayleyVectorJetPairRemainderPolynomial
    (extent : Nat) (left right : Z4Plaq) : RatPoly :=
  let leftQuadratic := globalCayleyVectorJetQuadraticPolynomial extent left
  let rightQuadratic := globalCayleyVectorJetQuadraticPolynomial extent right
  let leftRemainder := globalCayleyVectorJetRemainderPolynomial extent left
  let rightRemainder := globalCayleyVectorJetRemainderPolynomial extent right
  polyAdd
    (polyMul leftQuadratic rightRemainder)
    (polyAdd
      (polyMul leftRemainder rightQuadratic)
      (polyMul leftRemainder rightRemainder))

/-- Exact arbitrary-insertion carrier split of the two cleared vector jets
into the quadratic--quadratic pair plus the three residual products. -/
theorem globalCayleyVectorJetPair_quadratic_remainder_carrier
    {extent : Nat} {left right : Z4Plaq}
    (hleft : left ∈ boundaryCompleteSlabPlaquettes extent)
    (hright : right ∈ boundaryCompleteSlabPlaquettes extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetPairClearedPolynomial extent left right)
      (polyAdd
        (polyMul
          (globalCayleyVectorJetQuadraticPolynomial extent left)
          (globalCayleyVectorJetQuadraticPolynomial extent right))
        (globalCayleyVectorJetPairRemainderPolynomial extent left right)) := by
  let leftQuadratic := globalCayleyVectorJetQuadraticPolynomial extent left
  let rightQuadratic := globalCayleyVectorJetQuadraticPolynomial extent right
  let leftRemainder := globalCayleyVectorJetRemainderPolynomial extent left
  let rightRemainder := globalCayleyVectorJetRemainderPolynomial extent right
  have hleftSplit := globalCayleyVectorJet_quadratic_remainder_carrier hleft
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetClearedPolynomial extent left)
    (polyAdd leftQuadratic leftRemainder) at hleftSplit
  have hrightSplit := globalCayleyVectorJet_quadratic_remainder_carrier hright
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetClearedPolynomial extent right)
    (polyAdd rightQuadratic rightRemainder) at hrightSplit
  have hproduct := HaarCarrierEqv.mul hleftSplit hrightSplit
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetPairClearedPolynomial extent left right)
    (polyMul (polyAdd leftQuadratic leftRemainder)
      (polyAdd rightQuadratic rightRemainder)) at hproduct
  have hregroup : RatPolyCoeffEqv
      (polyMul (polyAdd leftQuadratic leftRemainder)
        (polyAdd rightQuadratic rightRemainder))
      (polyAdd (polyMul leftQuadratic rightQuadratic)
        (globalCayleyVectorJetPairRemainderPolynomial extent left right)) := by
    unfold globalCayleyVectorJetPairRemainderPolynomial
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

/-- Normalized ORIGINAL expectation of the two cleared vector jets. -/
def globalCayleyVectorJetPairClearedExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetPairClearedPolynomial
      (centralExtent half) left right)

/-- Normalized ORIGINAL expectation of the isolated quadratic--quadratic
pair. -/
def globalCayleyVectorJetPairQuadraticExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (polyMul
      (globalCayleyVectorJetQuadraticPolynomial (centralExtent half) left)
      (globalCayleyVectorJetQuadraticPolynomial (centralExtent half) right))

/-- Normalized ORIGINAL expectation of the three exact pair residual
products. -/
def globalCayleyVectorJetPairRemainderExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyVectorJetPairRemainderPolynomial
      (centralExtent half) left right)

/-- The two-plaquette carrier split passes exactly to the normalized ORIGINAL
expectation. -/
theorem globalCayleyVectorJetPair_originalExpectation_split
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : Z4Plaq)
    (hleft : left ∈ boundaryCompleteSlabPlaquettes (centralExtent half))
    (hright : right ∈ boundaryCompleteSlabPlaquettes (centralExtent half)) :
    CReal.Equiv
      (globalCayleyVectorJetPairClearedExpectation
        w hw0 hw1 half left right)
      (CReal.add
        (globalCayleyVectorJetPairQuadraticExpectation
          w hw0 hw1 half left right)
        (globalCayleyVectorJetPairRemainderExpectation
          w hw0 hw1 half left right)) := by
  let extent := centralExtent half
  let quadraticPair := polyMul
    (globalCayleyVectorJetQuadraticPolynomial extent left)
    (globalCayleyVectorJetQuadraticPolynomial extent right)
  let remainder := globalCayleyVectorJetPairRemainderPolynomial
    extent left right
  have hcarrier := globalCayleyVectorJetPair_quadratic_remainder_carrier
    hleft hright
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleyVectorJetPairClearedPolynomial extent left right)
    (polyAdd quadraticPair remainder) at hcarrier
  have hcongr := BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half hcarrier
  exact hcongr.trans (by
    simpa [globalCayleyVectorJetPairClearedExpectation,
      globalCayleyVectorJetPairQuadraticExpectation,
      globalCayleyVectorJetPairRemainderExpectation, extent, quadraticPair,
      remainder] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half quadraticPair remainder)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetPair

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetPair.globalCayleyVectorJetPair_quadratic_remainder_carrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetPair.globalCayleyVectorJetPair_originalExpectation_split
