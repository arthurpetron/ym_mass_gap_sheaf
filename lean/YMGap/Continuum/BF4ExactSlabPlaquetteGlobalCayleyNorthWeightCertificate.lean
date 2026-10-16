/-
# Same-Haar certificates for the normalized north weight and its deficit

Each normalized north base `(1 + r) / 2` is placed in the constructive
interval `[0,1]` on the ORIGINAL product-Haar carrier.  The four bases, their
product and its fourteenth power are then bounded by repeated multiplication
of intervals with their shared variables retained.  The pure plaquette vector
jet receives its own square certificate and unit upper bound.  Consequently
the literal north-weight deficit `(1 - P^14) V`, including its exact `2^66`
scale and positive bulk coefficients, has a sum-of-squares certificate under
the same ORIGINAL law.

No pointwise-to-Haar positivity principle, independence assumption,
southern-tail estimate, multi-chart partition, cutoff removal, continuum
theory, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
import YMGap.Continuum.BF4ExactSlabPolynomialExpectation
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private theorem supported_neg_local {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hp source hsource

private theorem supported_smul_local {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term hterm
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hterm
  exact hp source hsource

private def scalarReflection (q : PolyQuaternion) : PolyQuaternion where
  scalar := polyNeg q.scalar
  iPart := q.iPart
  jPart := q.jPart
  kPart := q.kPart

private theorem supported_scalarReflection {blocks : Nat} {q : PolyQuaternion}
    (hq : Supported blocks q) : Supported blocks (scalarReflection q) :=
  ⟨supported_neg_local hq.scalar, hq.iPart, hq.jPart, hq.kPart⟩

private theorem polyQuaternionNorm_scalarReflection (q : PolyQuaternion) :
    RatPolyCoeffEqv (polyQuaternionNorm (scalarReflection q))
      (polyQuaternionNorm q) := by
  unfold scalarReflection polyQuaternionNorm
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.add (.mul (.var 1) (.var 1))
        (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
    (.add (.mul (.var 0) (.var 0))
      (.add (.mul (.var 1) (.var 1))
        (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
    (by decide)
    (fun | 0 => q.scalar | 1 => q.iPart | 2 => q.jPart | _ => q.kPart)

/-- The south scalar base `1-r`, used as the explicit complement of the
normalized north base. -/
def oneSubScalarPolynomial (q : PolyQuaternion) : RatPoly :=
  polyAdd polyOne (polyNeg q.scalar)

/-- The same four-square construction as for `1+r`, applied after reflecting
only the scalar coordinate. -/
def oneSubScalar_certificate {blocks : Nat} {q : PolyQuaternion}
    (hq : Supported blocks q)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    Certificate blocks (oneSubScalarPolynomial q) := by
  have hreflectedNorm : HaarCarrierEqv blocks
      (polyQuaternionNorm (scalarReflection q)) polyOne :=
    (RatPolyCoeffEqv.haarCarrier
      (polyQuaternionNorm_scalarReflection q)).trans hnorm
  simpa [oneSubScalarPolynomial, oneAddScalar, scalarReflection] using
    (oneAddScalar_certificate (supported_scalarReflection hq) hreflectedNorm)

/-- The normalized north base itself has a positive certificate. -/
def northCayleyBasePolynomial_certificate {blocks : Nat} {q : PolyQuaternion}
    (hq : Supported blocks q)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    Certificate blocks (northCayleyBasePolynomial q) := by
  simpa [northCayleyBasePolynomial, cayleyChartDenominatorPolynomial,
    oneAddScalar] using
    (Certificate.smul half half_nonneg (oneAddScalar_certificate hq hnorm))

/-- The normalized south complement `(1-r)/2` has a positive certificate. -/
def southCayleyBasePolynomial_certificate {blocks : Nat} {q : PolyQuaternion}
    (hq : Supported blocks q)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    Certificate blocks (polySmul half (oneSubScalarPolynomial q)) :=
  Certificate.smul half half_nonneg (oneSubScalar_certificate hq hnorm)

private def scalarInterval {blocks : Nat} {q : PolyQuaternion}
    (hq : Supported blocks q)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    Interval blocks q.scalar 1 where
  support := hq.scalar
  nonnegative := Q'.zero_le_one
  upper := Certificate.ofCoeff
    ((RatPolyCoeffEqv.one_smul polyOne).add
      (RatPolyCoeffEqv.refl (polyNeg q.scalar)))
    (oneSubScalar_certificate hq hnorm)
  lower := Certificate.ofCoeff
    ((RatPolyCoeffEqv.one_smul polyOne).add
      (RatPolyCoeffEqv.refl q.scalar))
    (oneAddScalar_certificate hq hnorm)

private theorem northCayleyBasePolynomial_coeff_affine (q : PolyQuaternion) :
    RatPolyCoeffEqv (northCayleyBasePolynomial q)
      (polyAdd (cap half) (polySmul half q.scalar)) := by
  unfold northCayleyBasePolynomial cayleyChartDenominatorPolynomial cap
  exact RatPolyCoeffEqv.smul_add half polyOne q.scalar

/-- A unit-norm supported quaternion has its normalized north scalar base in
the SAME-Haar interval with symmetric cap one.  In particular, both the base
and its literal complement are certificate-positive under every insertion. -/
def northCayleyBasePolynomial_interval {blocks : Nat} {q : PolyQuaternion}
    (hq : Supported blocks q)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne) :
    Interval blocks (northCayleyBasePolynomial q) 1 := by
  let scalarPart : Interval blocks (polySmul half q.scalar) (half * 1) :=
    (scalarInterval hq hnorm).smul half half_nonneg
  let affine : Interval blocks
      (polyAdd (cap half) (polySmul half q.scalar)) (half + half * 1) :=
    (Interval.constant blocks half half_nonneg).add scalarPart
  exact Interval.ofCoeff
    (supported_smul_local
      (supported_add (supported_one blocks) hq.scalar) half)
    (northCayleyBasePolynomial_coeff_affine q)
    (Interval.changeCap (by decide) affine)

/-- Support for every oriented corrected slab link, including identity
fallback entries outside the finite slab list. -/
theorem supported_orientedCorrectedSlabLinkPolynomial
    (extent : Nat) (entry : OrientedBF4Link) :
    Supported (boundaryCompleteSlabLinks extent).length
      (orientedCorrectedSlabLinkPolynomial extent entry) := by
  unfold orientedCorrectedSlabLinkPolynomial
  split
  · exact (supported_slabLink extent entry.link).conj
  · exact supported_slabLink extent entry.link

/-- Every oriented corrected slab link has a certified normalized north base
in the unit interval on the complete slab Haar carrier. -/
def orientedNorthCayleyBasePolynomial_interval
    (extent : Nat) (entry : OrientedBF4Link) :
    Interval (boundaryCompleteSlabLinks extent).length
      (northCayleyBasePolynomial
        (orientedCorrectedSlabLinkPolynomial extent entry)) 1 :=
  northCayleyBasePolynomial_interval
    (supported_orientedCorrectedSlabLinkPolynomial extent entry)
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent entry)

/-- Every oriented north base is itself certificate-positive, separately from
its unit upper certificate. -/
def orientedNorthCayleyBasePolynomial_certificate
    (extent : Nat) (entry : OrientedBF4Link) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (northCayleyBasePolynomial
        (orientedCorrectedSlabLinkPolynomial extent entry)) :=
  northCayleyBasePolynomial_certificate
    (supported_orientedCorrectedSlabLinkPolynomial extent entry)
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent entry)

/-- The balanced four-link normalized north product is in the SAME-Haar unit
interval without any disjoint-support or independence premise. -/
def globalCayleyNorthBaseProduct_interval
    (extent : Nat) (face : Z4Plaq) :
    Interval (boundaryCompleteSlabLinks extent).length
      (globalCayleyNorthBaseProduct extent face) 1 := by
  let I0 := orientedNorthCayleyBasePolynomial_interval extent
    (faceCayleyEntry0 face)
  let I1 := orientedNorthCayleyBasePolynomial_interval extent
    (faceCayleyEntry1 face)
  let I2 := orientedNorthCayleyBasePolynomial_interval extent
    (faceCayleyEntry2 face)
  let I3 := orientedNorthCayleyBasePolynomial_interval extent
    (faceCayleyEntry3 face)
  simpa [globalCayleyNorthBaseProduct, faceCayleyQuaternion0,
    faceCayleyQuaternion1, faceCayleyQuaternion2, faceCayleyQuaternion3]
    using Interval.changeCap
      (by decide : Q'.eqv ((1 : Q') * 1 * (1 * 1)) 1)
      ((I0.mul I1).mul (I2.mul I3))

/-- The balanced four-link north product is certificate-positive with all
shared coordinates retained. -/
def globalCayleyNorthBaseProduct_certificate
    (extent : Nat) (face : Z4Plaq) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleyNorthBaseProduct extent face) := by
  let C0 := orientedNorthCayleyBasePolynomial_certificate extent
    (faceCayleyEntry0 face)
  let C1 := orientedNorthCayleyBasePolynomial_certificate extent
    (faceCayleyEntry1 face)
  let C2 := orientedNorthCayleyBasePolynomial_certificate extent
    (faceCayleyEntry2 face)
  let C3 := orientedNorthCayleyBasePolynomial_certificate extent
    (faceCayleyEntry3 face)
  simpa [globalCayleyNorthBaseProduct, faceCayleyQuaternion0,
    faceCayleyQuaternion1, faceCayleyQuaternion2, faceCayleyQuaternion3]
    using (C0.mul C1).mul (C2.mul C3)

private def unitIntervalPower {blocks : Nat} {p : RatPoly}
    (P : Interval blocks p 1) : ∀ exponent,
    Interval blocks (coeffPolyPow p exponent) 1
  | 0 => Interval.one blocks
  | exponent + 1 =>
      Interval.changeCap (by decide : Q'.eqv ((1 : Q') * 1) 1)
        ((unitIntervalPower P exponent).mul P)

private def certificatePower {blocks : Nat} {p : RatPoly}
    (P : Certificate blocks p) : ∀ exponent,
    Certificate blocks (coeffPolyPow p exponent)
  | 0 => Certificate.one blocks
  | exponent + 1 => (certificatePower P exponent).mul P

/-- The literal fourteenth power of the four-link north product remains in
the unit interval on the same ORIGINAL Haar carrier. -/
def globalCayleyNorthBasePower14_interval
    (extent : Nat) (face : Z4Plaq) :
    Interval (boundaryCompleteSlabLinks extent).length
      (globalCayleyNorthBasePower14 extent face) 1 := by
  unfold globalCayleyNorthBasePower14
  exact unitIntervalPower (globalCayleyNorthBaseProduct_interval extent face) 14

/-- The literal fourteenth power is also certificate-positive, independently
of the upper certificate for `1-P^14`. -/
def globalCayleyNorthBasePower14_certificate
    (extent : Nat) (face : Z4Plaq) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleyNorthBasePower14 extent face) := by
  unfold globalCayleyNorthBasePower14
  exact certificatePower
    (globalCayleyNorthBaseProduct_certificate extent face) 14

/-- Haar-unit norm for the literal corrected plaquette word for every face.
The all-face form uses the already verified identity fallback for each link. -/
theorem haarNorm_slabPlaquette_all (extent : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm (correctedSlabPlaquettePolynomial extent face))
      polyOne := by
  exact haarNorm_fold (orientedCorrectedSlabLinkPolynomial extent)
    (orientedPlaquetteBoundary face)
    (fun entry _ =>
      haarNorm_orientedCorrectedSlabLinkPolynomial extent entry)
    PolyQuaternion.one
    (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one)

/-- The pure vector jet is the explicit sum of its three coordinate squares. -/
def globalPlaquetteVectorJet_certificate
    (extent : Nat) (face : Z4Plaq) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalPlaquetteVectorJet extent face) := by
  let q := correctedSlabPlaquettePolynomial extent face
  have hq := supported_slabPlaquette extent face
  exact (Certificate.square q.iPart hq.iPart).add
    ((Certificate.square q.jPart hq.jPart).add
      (Certificate.square q.kPart hq.kPart))

private theorem globalPlaquetteVectorJet_upper_carrier
    (extent : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyAdd (cap 1)
        (polyNeg (globalPlaquetteVectorJet extent face)))
      (polyMul (correctedSlabPlaquettePolynomial extent face).scalar
        (correctedSlabPlaquettePolynomial extent face).scalar) := by
  let blocks := (boundaryCompleteSlabLinks extent).length
  let q := correctedSlabPlaquettePolynomial extent face
  let vectorJet := globalPlaquetteVectorJet extent face
  have hnorm : HaarCarrierEqv blocks (polyQuaternionNorm q) polyOne :=
    haarNorm_slabPlaquette_all extent face
  have hreplace : HaarCarrierEqv blocks
      (polyAdd (cap 1) (polyNeg vectorJet))
      (polyAdd (polyQuaternionNorm q) (polyNeg vectorJet)) :=
    HaarCarrierEqv.add
      ((RatPolyCoeffEqv.haarCarrier
        (RatPolyCoeffEqv.one_smul polyOne)).trans hnorm.symm)
      (HaarCarrierEqv.refl _ _)
  have hcancel : RatPolyCoeffEqv
      (polyAdd (polyQuaternionNorm q) (polyNeg vectorJet))
      (polyMul q.scalar q.scalar) := by
    dsimp only [q, vectorJet, globalPlaquetteVectorJet,
      polyQuaternionNorm]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.mul (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 1))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
        (.neg
          (.add (.mul (.var 1) (.var 1))
            (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))))
      (.mul (.var 0) (.var 0))
      (by decide)
      (fun
        | 0 => (correctedSlabPlaquettePolynomial extent face).scalar
        | 1 => (correctedSlabPlaquettePolynomial extent face).iPart
        | 2 => (correctedSlabPlaquettePolynomial extent face).jPart
        | _ => (correctedSlabPlaquettePolynomial extent face).kPart)
  exact hreplace.trans (RatPolyCoeffEqv.haarCarrier hcancel)

/-- The pure plaquette vector jet is in the SAME-Haar interval `[0,1]`. -/
def globalPlaquetteVectorJet_interval
    (extent : Nat) (face : Z4Plaq) :
    Interval (boundaryCompleteSlabLinks extent).length
      (globalPlaquetteVectorJet extent face) 1 := by
  let q := correctedSlabPlaquettePolynomial extent face
  let hq := supported_slabPlaquette extent face
  let vectorCertificate := globalPlaquetteVectorJet_certificate extent face
  exact
    { support := supported_add
        (supported_polyMul hq.iPart hq.iPart)
        (supported_add
          (supported_polyMul hq.jPart hq.jPart)
          (supported_polyMul hq.kPart hq.kPart))
      nonnegative := Q'.zero_le_one
      upper := Certificate.transport
        (globalPlaquetteVectorJet_upper_carrier extent face)
        (Certificate.square q.scalar hq.scalar)
      lower := (Certificate.constant
        (boundaryCompleteSlabLinks extent).length 1 Q'.zero_le_one).add
        vectorCertificate }

/-- The exact facewise north-weight deficit, including its `2^66` scale, is
certificate-positive under every ORIGINAL Haar insertion. -/
def globalCayleyVectorJetNorthWeightDeficit_certificate
    (extent : Nat) (face : Z4Plaq) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetNorthWeightDeficitPolynomial extent face) := by
  let blocks := (boundaryCompleteSlabLinks extent).length
  let weight := globalCayleyNorthBasePower14 extent face
  let vectorJet := globalPlaquetteVectorJet extent face
  have hweight : Certificate blocks
      (polyAdd polyOne (polyNeg weight)) :=
    Certificate.ofCoeff
      ((RatPolyCoeffEqv.one_smul polyOne).symm.add
        (RatPolyCoeffEqv.refl (polyNeg weight)))
      (globalCayleyNorthBasePower14_interval extent face).upper
  have hproduct : Certificate blocks
      (polyMul (polyAdd polyOne (polyNeg weight)) vectorJet) :=
    hweight.mul (globalPlaquetteVectorJet_certificate extent face)
  have hscale : (0 : Q') ≤ globalCayleyVectorJetNorthWeightScale := by
    unfold globalCayleyVectorJetNorthWeightScale
    decide
  simpa [globalCayleyVectorJetNorthWeightDeficitPolynomial, blocks,
    weight, vectorJet] using
    (Certificate.constant blocks globalCayleyVectorJetNorthWeightScale
      hscale).mul hproduct

/-- Actual same-Haar positivity of the face deficit after an arbitrary
supported square insertion. -/
theorem globalCayleyVectorJetNorthWeightDeficit_square_insertion_nonnegative
    (extent : Nat) (face : Z4Plaq) (r : RatPoly)
    (hr : SupportedQuaternionBlocks
      (boundaryCompleteSlabLinks extent).length r) :
    (0 : Q') ≤
      BF4GeometricHaarMehlerProjection.quaternionHaar
        (boundaryCompleteSlabLinks extent).length
        (polyMul (polyMul r r)
          (globalCayleyVectorJetNorthWeightDeficitPolynomial extent face)) :=
  Certificate.square_insertion_nonnegative
    (globalCayleyVectorJetNorthWeightDeficit_certificate extent face) r hr

private def finiteWeightedCertificate {Index : Type} {blocks : Nat}
    (coefficient : Index → Q') (polynomial : Index → RatPoly)
    (certificate : ∀ index, Certificate blocks (polynomial index)) :
    ∀ items : List Index,
      (∀ index, index ∈ items → (0 : Q') ≤ coefficient index) →
      Certificate blocks
        (BF4ExactPhysicalCenteredVacuumHaarResummation.finitePolySum
          (fun index => polySmul (coefficient index) (polynomial index))
          items)
  | [], _ => Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
      (Certificate.constant blocks 0 (Q'.le_refl' _))
  | index :: items, hnonnegative =>
      (Certificate.smul (coefficient index)
        (hnonnegative index List.mem_cons_self) (certificate index)).add
      (finiteWeightedCertificate coefficient polynomial certificate items
        (fun next hnext =>
          hnonnegative next (List.mem_cons_of_mem index hnext)))

/-- The complete positive-coefficient bulk north deficit has one constructive
certificate on the complete ORIGINAL slab Haar carrier. -/
def globalCayleyVectorJetBulkNorthWeightDeficit_certificate
    (s : Nat) (hs : 0 < s) (extent time : Nat) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkNorthWeightDeficitSource
        s hs extent time) := by
  apply finiteWeightedCertificate
  · intro face
    exact globalCayleyVectorJetNorthWeightDeficit_certificate extent
      (timeShiftPlaquette time face)
  · intro face hface
    exact Q'.le_of_lt (bulkSourceCoefficient_pos hs hface)

/-- The certified bulk north deficit has nonnegative expectation under the
unchanged normalized ORIGINAL slab action. -/
theorem globalCayleyVectorJetBulkNorthWeightDeficit_expectation_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (halfTime s : Nat) (hs : 0 < s) (time : Nat) :
    CReal.leEv (CReal.ofQ' 0)
      (expectation w hw0 hw1 halfTime
        (globalCayleyVectorJetBulkNorthWeightDeficitSource
          s hs (centralExtent halfTime) time)) :=
  expectation_certificate_nonnegative w hw0 hw1 halfTime _
    (globalCayleyVectorJetBulkNorthWeightDeficit_certificate
      s hs (centralExtent halfTime) time)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.oneSubScalar_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.northCayleyBasePolynomial_interval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.supported_orientedCorrectedSlabLinkPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.globalCayleyNorthBaseProduct_interval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.globalCayleyNorthBaseProduct_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.globalCayleyNorthBasePower14_interval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.globalCayleyNorthBasePower14_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.haarNorm_slabPlaquette_all
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.globalPlaquetteVectorJet_interval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.globalCayleyVectorJetNorthWeightDeficit_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.globalCayleyVectorJetNorthWeightDeficit_square_insertion_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.globalCayleyVectorJetBulkNorthWeightDeficit_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate.globalCayleyVectorJetBulkNorthWeightDeficit_expectation_nonnegative
