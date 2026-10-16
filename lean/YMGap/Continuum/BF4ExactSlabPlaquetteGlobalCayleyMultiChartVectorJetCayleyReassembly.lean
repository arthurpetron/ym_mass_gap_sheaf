/-
# Exact signed-chart Cayley reassembly of the physical vector jet

For every fixed four-link chart, the signed word has the same vector norm as
the physical plaquette word.  Its actual signed clearing scale therefore
satisfies the universal scalar/vector identity

  4 * S^2 * V = 4 * S * Delta - Delta^2,
  Delta = S * (2 - 2 * scalar).

Multiplication by the certified subordinate quotient and summation over all
sixteen charts gives a lossless Cayley-deficit representation of the
identity-scaled physical vector jet on the unchanged ORIGINAL Haar carrier.

No homogeneous Cayley truncation, remainder estimate, law comparison,
cutoff removal, continuum Hamiltonian, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetCayleyReassembly

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPartition
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

/-- Scalar coordinate of the signed chart word. -/
def globalCayleySignedChartScalar
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  (globalCayleySignedChartQuaternionWord extent face chart).scalar

/-- Actual signed-chart cleared scalar deficit
`S_s * (2 - 2 * scalar_s)`. -/
def globalCayleySignedChartDeficitPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (globalCayleySignedChartScaleProduct extent face chart)
    (polyAdd (polyConst 2)
      (polyNeg (polyMul (polyConst 2)
        (globalCayleySignedChartScalar extent face chart))))

/-- The universal cleared vector-jet expression in the signed chart. -/
def globalCayleySignedChartCayleyVectorJetPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  let scale := globalCayleySignedChartScaleProduct extent face chart
  let deficit := globalCayleySignedChartDeficitPolynomial extent face chart
  polyAdd
    (polyMul (polyMul (polyConst 4) scale) deficit)
    (polyNeg (polyMul deficit deficit))

private theorem signedChartQuaternion_scalar_square
    (south : Bool) (q : PolyQuaternion) :
    RatPolyCoeffEqv
      (polyMul (signedChartQuaternion south q).scalar
        (signedChartQuaternion south q).scalar)
      (polyMul q.scalar q.scalar) := by
  cases south
  · exact RatPolyCoeffEqv.refl _
  · change RatPolyCoeffEqv
      (polyMul (polyNeg q.scalar) (polyNeg q.scalar))
      (polyMul q.scalar q.scalar)
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.mul (.var 0) (.var 0))
      (by decide) (fun _ => q.scalar)

/-- The signed chart vector jet is the complement of the signed word scalar
square on the complete finite ORIGINAL Haar carrier. -/
theorem globalCayleySignedChartVectorJet_scalar_complement
    {extent : Nat} {face : Z4Plaq} (chart : FourCayleyChart)
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartVectorJet extent face chart)
      (polyAdd polyOne
        (polyNeg
          (polyMul
            (globalCayleySignedChartScalar extent face chart)
            (globalCayleySignedChartScalar extent face chart)))) := by
  let signedWord := globalCayleySignedChartQuaternionWord extent face chart
  let faceWord := faceCayleyQuaternionWord extent face
  let originalWord := correctedSlabPlaquettePolynomial extent face
  have hsector := globalCayleySignedChartQuaternionWord_coeff_sector
    extent face chart
  have horiginal :=
    correctedSlabPlaquettePolynomial_coeff_faceCayleyQuaternionWord
      extent face
  have hsquare : RatPolyCoeffEqv
      (polyMul signedWord.scalar signedWord.scalar)
      (polyMul originalWord.scalar originalWord.scalar) :=
    (hsector.scalar.mul hsector.scalar).trans
      ((signedChartQuaternion_scalar_square chart.sector faceWord).trans
        (horiginal.scalar.symm.mul horiginal.scalar.symm))
  have hvector : HaarCarrierEqv
      (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartVectorJet extent face chart)
      (globalPlaquetteVectorJet extent face) :=
    RatPolyCoeffEqv.haarCarrier
      (globalCayleySignedChartVectorJet_coeff_original extent face chart)
  have hcomplement := globalPlaquetteVectorJet_scalar_complement hface
  have hreplace : RatPolyCoeffEqv
      (polyAdd polyOne
        (polyNeg (polyMul originalWord.scalar originalWord.scalar)))
      (polyAdd polyOne
        (polyNeg (polyMul signedWord.scalar signedWord.scalar))) :=
    (RatPolyCoeffEqv.refl polyOne).add
      (RatPolyCoeffEqv.neg hsquare.symm)
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleySignedChartVectorJet extent face chart)
    (polyAdd polyOne
      (polyNeg (polyMul signedWord.scalar signedWord.scalar)))
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalPlaquetteVectorJet extent face)
    (polyAdd polyOne
      (polyNeg (polyMul originalWord.scalar originalWord.scalar))) at hcomplement
  exact hvector.trans
    (hcomplement.trans (RatPolyCoeffEqv.haarCarrier hreplace))

/-- In every fixed signed chart, the actual denominator-square clearing obeys
the exact Cayley scalar/vector identity. -/
theorem globalCayleySignedChartVectorJetCleared_carrier_cayley
    {extent : Nat} {face : Z4Plaq} (chart : FourCayleyChart)
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartVectorJetClearedPolynomial extent face chart)
      (globalCayleySignedChartCayleyVectorJetPolynomial
        extent face chart) := by
  let scale := globalCayleySignedChartScaleProduct extent face chart
  let scalar := globalCayleySignedChartScalar extent face chart
  let vectorJet := globalCayleySignedChartVectorJet extent face chart
  let scalarProxy := polyAdd polyOne
    (polyNeg (polyMul scalar scalar))
  let delta := polyAdd (polyConst 2)
    (polyNeg (polyMul (polyConst 2) scalar))
  let deficit := polyMul scale delta
  let clearedFactor := polyMul (polyConst 4)
    (polyMul scale scale)
  have hjet := globalCayleySignedChartVectorJet_scalar_complement
    chart hface
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    vectorJet scalarProxy at hjet
  have hleft : HaarCarrierEqv
      (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartVectorJetClearedPolynomial extent face chart)
      (polyMul clearedFactor scalarProxy) := by
    unfold globalCayleySignedChartVectorJetClearedPolynomial clearedFactor
    exact HaarCarrierEqv.mul_left _ hjet
  have hcore : RatPolyCoeffEqv
      (polyMul clearedFactor scalarProxy)
      (polyAdd
        (polyMul (polyMul (polyConst 4) scale) deficit)
        (polyNeg (polyMul deficit deficit))) := by
    unfold clearedFactor scalarProxy deficit delta
    exact coeffEvalExpr_eqv_of_normalize_eq
      ((4 * (.var 0 * .var 0)) * (1 + -(.var 1 * .var 1)))
      ((4 * .var 0) * (.var 0 * (2 + -(2 * .var 1))) +
        -((.var 0 * (2 + -(2 * .var 1))) *
          (.var 0 * (2 + -(2 * .var 1)))))
      (by decide)
      (fun | 0 => scale | _ => scalar)
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleySignedChartVectorJetClearedPolynomial extent face chart)
    (polyAdd
      (polyMul (polyMul (polyConst 4) scale) deficit)
      (polyNeg (polyMul deficit deficit)))
  exact hleft.trans (RatPolyCoeffEqv.haarCarrier hcore)

/-- Subordinate-quotient-weighted signed-chart Cayley expression. -/
def globalCayleySignedChartCayleyReassemblyTerm
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (globalCayleySubordinateChartQuotientPolynomial extent face chart)
    (globalCayleySignedChartCayleyVectorJetPolynomial extent face chart)

def globalCayleySignedChartCayleyReassemblyPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  finitePolySum
    (globalCayleySignedChartCayleyReassemblyTerm extent face)
    fourCayleyChartTable

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

/-- The quotient-weighted sixteen-chart Cayley expressions reconstruct the
identity-scaled physical vector jet without chart loss. -/
theorem globalCayleySignedChartCayleyReassembly_carrier_identityScaled
    {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartCayleyReassemblyPolynomial extent face)
      (polyMul (polySmul (Q'.ofInt (2 ^ 66)) polyOne)
        (globalPlaquetteVectorJet extent face)) := by
  have hsum := finiteSum_carrier
    (boundaryCompleteSlabLinks extent).length
    (globalCayleySignedChartReassemblyTerm extent face)
    (globalCayleySignedChartCayleyReassemblyTerm extent face)
    fourCayleyChartTable
    (fun chart _ => HaarCarrierEqv.mul
      (HaarCarrierEqv.refl _
        (globalCayleySubordinateChartQuotientPolynomial
          extent face chart))
      (globalCayleySignedChartVectorJetCleared_carrier_cayley
        chart hface))
  have hreassembly :=
    globalCayleySignedChartReassembly_carrier_identityScaled extent face
  exact hsum.symm.trans hreassembly

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetCayleyReassembly

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetCayleyReassembly.globalCayleySignedChartVectorJet_scalar_complement
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetCayleyReassembly.globalCayleySignedChartVectorJetCleared_carrier_cayley
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetCayleyReassembly.globalCayleySignedChartCayleyReassembly_carrier_identityScaled
