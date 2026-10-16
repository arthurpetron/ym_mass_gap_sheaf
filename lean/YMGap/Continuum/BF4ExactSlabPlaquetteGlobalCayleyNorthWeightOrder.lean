/-
# Same-Haar Bernoulli and vector-jet order for the north-weight deficit

The preceding certificates give `0 <= P <= 1`, `0 <= P^14 <= 1` and
`0 <= V <= 1` on the unchanged ORIGINAL Haar carrier.  This module lifts the
Bernoulli identity by a certificate recursion and combines it with the vector
upper certificate.  The exact face deficit is thereby bounded, in same-law
certificate order, by fourteen copies of the four-link north loss.

No estimate makes the remaining loss small.  In particular there is no
individual-link concentration claim, southern-tail estimate, multi-chart
partition, cutoff removal, continuum theory, or mass gap here.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightOrder

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
  (finitePolySum)
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightCertificate
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- The literal complement `1-p^n`. -/
def powerDeficitPolynomial (p : RatPoly) (exponent : Nat) : RatPoly :=
  polyAdd polyOne (polyNeg (coeffPolyPow p exponent))

/-- Repeated polynomial addition without introducing a new scalar
normalization convention. -/
def repeatedPolySum (p : RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | count + 1 => polyAdd (repeatedPolySum p count) p

/-- Certificate form of `n(1-p) - (1-p^n)`. -/
def bernoulliGapPolynomial (p : RatPoly) (exponent : Nat) : RatPoly :=
  polyAdd
    (repeatedPolySum (polyAdd polyOne (polyNeg p)) exponent)
    (polyNeg (powerDeficitPolynomial p exponent))

private def unitIntervalPower {blocks : Nat} {p : RatPoly}
    (P : Interval blocks p 1) : ∀ exponent,
    Interval blocks (coeffPolyPow p exponent) 1
  | 0 => Interval.one blocks
  | exponent + 1 =>
      Interval.changeCap (by decide : Q'.eqv ((1 : Q') * 1) 1)
        ((unitIntervalPower P exponent).mul P)

private def powerDeficit_certificate {blocks : Nat} {p : RatPoly}
    (P : Interval blocks p 1) (exponent : Nat) :
    Certificate blocks (powerDeficitPolynomial p exponent) :=
  Certificate.ofCoeff
    ((RatPolyCoeffEqv.one_smul polyOne).symm.add
      (RatPolyCoeffEqv.refl
        (polyNeg (coeffPolyPow p exponent))))
    (unitIntervalPower P exponent).upper

private theorem bernoulliGap_zero_coeff (p : RatPoly) :
    RatPolyCoeffEqv (bernoulliGapPolynomial p 0)
      (polySmul 0 polyOne) := by
  unfold bernoulliGapPolynomial repeatedPolySum powerDeficitPolynomial
    coeffPolyPow
  have hzero : RatPolyCoeffEqv
      (polyAdd polyZero (polyNeg (polyAdd polyOne (polyNeg polyOne))))
      polyZero := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 1) (.neg (.add (.var 0) (.neg (.var 0)))))
      (.var 1) (by decide)
      (fun | 0 => polyOne | _ => polyZero)
  exact hzero.trans (RatPolyCoeffEqv.zero_smul polyOne).symm

private theorem bernoulliGap_succ_coeff (p : RatPoly) (exponent : Nat) :
    RatPolyCoeffEqv
      (bernoulliGapPolynomial p (exponent + 1))
      (polyAdd
        (bernoulliGapPolynomial p exponent)
        (polyMul (polyAdd polyOne (polyNeg p))
          (powerDeficitPolynomial p exponent))) := by
  change RatPolyCoeffEqv
    (polyAdd
      (polyAdd
        (repeatedPolySum (polyAdd polyOne (polyNeg p)) exponent)
        (polyAdd polyOne (polyNeg p)))
      (polyNeg
        (polyAdd polyOne
          (polyNeg (polyMul (coeffPolyPow p exponent) p)))))
    (polyAdd
      (polyAdd
        (repeatedPolySum (polyAdd polyOne (polyNeg p)) exponent)
        (polyNeg
          (polyAdd polyOne
            (polyNeg (coeffPolyPow p exponent)))))
      (polyMul (polyAdd polyOne (polyNeg p))
        (polyAdd polyOne
          (polyNeg (coeffPolyPow p exponent)))))
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.add (.var 0) (.add (.const 1) (.neg (.var 1))))
      (.neg (.add (.const 1) (.neg (.mul (.var 2) (.var 1))))))
    (.add
      (.add (.var 0) (.neg (.add (.const 1) (.neg (.var 2)))))
      (.mul (.add (.const 1) (.neg (.var 1)))
        (.add (.const 1) (.neg (.var 2)))))
    (by decide)
    (fun
      | 0 => repeatedPolySum (polyAdd polyOne (polyNeg p)) exponent
      | 1 => p
      | _ => coeffPolyPow p exponent)

/-- Constructive Bernoulli: the difference
`n(1-p) - (1-p^n)` is certificate-positive whenever `p` has a SAME-Haar
unit interval. -/
def bernoulliGap_certificate {blocks : Nat} {p : RatPoly}
    (P : Interval blocks p 1) : ∀ exponent,
    Certificate blocks (bernoulliGapPolynomial p exponent)
  | 0 => Certificate.ofCoeff (bernoulliGap_zero_coeff p)
      (Certificate.constant blocks 0 (Q'.le_refl' _))
  | exponent + 1 => by
      have hbase : Certificate blocks (polyAdd polyOne (polyNeg p)) :=
        Certificate.ofCoeff
          ((RatPolyCoeffEqv.refl polyOne).add
            (RatPolyCoeffEqv.neg
              (RatPolyCoeffEqv.one_mul p).symm))
          (powerDeficit_certificate P 1)
      exact Certificate.ofCoeff
        (bernoulliGap_succ_coeff p exponent)
        ((bernoulliGap_certificate P exponent).add
          (hbase.mul (powerDeficit_certificate P exponent)))

/-- Fourteen copies of the four-link north loss minus its fourteenth-power
loss, written without changing the exact polynomial carrier. -/
def globalCayleyNorthBernoulliGapPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  bernoulliGapPolynomial
    (globalCayleyNorthBaseProduct extent face) 14

/-- SAME-Haar certificate for
`14(1-P) - (1-P^14)`. -/
def globalCayleyNorthBernoulliGap_certificate
    (extent : Nat) (face : Z4Plaq) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleyNorthBernoulliGapPolynomial extent face) :=
  bernoulliGap_certificate
    (globalCayleyNorthBaseProduct_interval extent face) 14

/-- The exact upper polynomial: `2^66` times fourteen copies of `1-P`. -/
def globalCayleyVectorJetNorthWeightUpperPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polySmul globalCayleyVectorJetNorthWeightScale polyOne)
    (repeatedPolySum
      (polyAdd polyOne
        (polyNeg (globalCayleyNorthBaseProduct extent face))) 14)

/-- Difference between the explicit upper polynomial and the exact face
north-weight deficit. -/
def globalCayleyVectorJetNorthWeightOrderGapPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyAdd
    (globalCayleyVectorJetNorthWeightUpperPolynomial extent face)
    (polyNeg
      (globalCayleyVectorJetNorthWeightDeficitPolynomial extent face))

private theorem globalCayleyVectorJetNorthWeightOrderGap_coeff
    (extent : Nat) (face : Z4Plaq) :
    let scale := polySmul globalCayleyVectorJetNorthWeightScale polyOne
    let product := globalCayleyNorthBaseProduct extent face
    let loss14 := powerDeficitPolynomial product 14
    let vectorJet := globalPlaquetteVectorJet extent face
    RatPolyCoeffEqv
      (globalCayleyVectorJetNorthWeightOrderGapPolynomial extent face)
      (polyAdd
        (polyMul scale
          (polyMul loss14
            (polyAdd polyOne (polyNeg vectorJet))))
        (polyMul scale
          (globalCayleyNorthBernoulliGapPolynomial extent face))) := by
  dsimp only
  unfold globalCayleyVectorJetNorthWeightOrderGapPolynomial
    globalCayleyVectorJetNorthWeightUpperPolynomial
    globalCayleyVectorJetNorthWeightDeficitPolynomial
    globalCayleyNorthBernoulliGapPolynomial bernoulliGapPolynomial
    powerDeficitPolynomial
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.mul (.var 0) (.var 1))
      (.neg (.mul (.var 0) (.mul (.var 2) (.var 3)))))
    (.add
      (.mul (.var 0)
        (.mul (.var 2) (.add (.const 1) (.neg (.var 3)))))
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))))
    (by decide)
    (fun
      | 0 => polySmul globalCayleyVectorJetNorthWeightScale polyOne
      | 1 => repeatedPolySum
          (polyAdd polyOne
            (polyNeg (globalCayleyNorthBaseProduct extent face))) 14
      | 2 => polyAdd polyOne
          (polyNeg
            (globalCayleyNorthBasePower14 extent face))
      | _ => globalPlaquetteVectorJet extent face)

/-- The exact facewise inequality

`2^66 (1-P^14) V <= 2^66 * 14 (1-P)`

is represented by a constructive certificate for the difference, on the
unchanged ORIGINAL Haar carrier. -/
def globalCayleyVectorJetNorthWeightOrderGap_certificate
    (extent : Nat) (face : Z4Plaq) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetNorthWeightOrderGapPolynomial extent face) := by
  let blocks := (boundaryCompleteSlabLinks extent).length
  let product := globalCayleyNorthBaseProduct extent face
  let loss14 := powerDeficitPolynomial product 14
  let vectorJet := globalPlaquetteVectorJet extent face
  have hloss14 : Certificate blocks loss14 :=
    powerDeficit_certificate
      (globalCayleyNorthBaseProduct_interval extent face) 14
  have hvectorUpper : Certificate blocks
      (polyAdd polyOne (polyNeg vectorJet)) :=
    Certificate.ofCoeff
      ((RatPolyCoeffEqv.one_smul polyOne).symm.add
        (RatPolyCoeffEqv.refl (polyNeg vectorJet)))
      (globalPlaquetteVectorJet_interval extent face).upper
  have hscale : (0 : Q') ≤ globalCayleyVectorJetNorthWeightScale := by
    unfold globalCayleyVectorJetNorthWeightScale
    decide
  have hvectorGap : Certificate blocks
      (polyMul
        (polySmul globalCayleyVectorJetNorthWeightScale polyOne)
        (polyMul loss14 (polyAdd polyOne (polyNeg vectorJet)))) :=
    (Certificate.constant blocks globalCayleyVectorJetNorthWeightScale
      hscale).mul (hloss14.mul hvectorUpper)
  have hbernoulliGap : Certificate blocks
      (polyMul
        (polySmul globalCayleyVectorJetNorthWeightScale polyOne)
        (globalCayleyNorthBernoulliGapPolynomial extent face)) :=
    (Certificate.constant blocks globalCayleyVectorJetNorthWeightScale
      hscale).mul
      (globalCayleyNorthBernoulliGap_certificate extent face)
  exact Certificate.ofCoeff
    (globalCayleyVectorJetNorthWeightOrderGap_coeff extent face)
    (hvectorGap.add hbernoulliGap)

private def finiteWeightedCertificate {Index : Type} {blocks : Nat}
    (coefficient : Index → Q') (polynomial : Index → RatPoly)
    (certificate : ∀ index, Certificate blocks (polynomial index)) :
    ∀ items : List Index,
      (∀ index, index ∈ items → (0 : Q') ≤ coefficient index) →
      Certificate blocks
        (finitePolySum
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

/-- Positive-coefficient bulk sum of the facewise order gaps. -/
def globalCayleyVectorJetBulkNorthWeightOrderGapSource
    (s : Nat) (hs : 0 < s) (extent time : Nat) : RatPoly :=
  finitePolySum
    (fun face => polySmul (bulkSourceCoefficient s hs face)
      (globalCayleyVectorJetNorthWeightOrderGapPolynomial extent
        (timeShiftPlaquette time face)))
    (bulkSourceFaces s)

/-- The complete bulk order gap has one constructive certificate on the
unchanged ORIGINAL slab Haar carrier. -/
def globalCayleyVectorJetBulkNorthWeightOrderGap_certificate
    (s : Nat) (hs : 0 < s) (extent time : Nat) :
    Certificate (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetBulkNorthWeightOrderGapSource
        s hs extent time) := by
  apply finiteWeightedCertificate
  · intro face
    exact globalCayleyVectorJetNorthWeightOrderGap_certificate extent
      (timeShiftPlaquette time face)
  · intro face hface
    exact Q'.le_of_lt (bulkSourceCoefficient_pos hs hface)

/-- Under the SAME normalized ORIGINAL action, the bulk difference between
the explicit fourteen-loss upper source and the exact north-weight deficit is
nonnegative.  This is the action-level order statement; no smallness of the
remaining loss is asserted. -/
theorem globalCayleyVectorJetBulkNorthWeightOrderGap_expectation_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (halfTime s : Nat) (hs : 0 < s) (time : Nat) :
    CReal.leEv (CReal.ofQ' 0)
      (expectation w hw0 hw1 halfTime
        (globalCayleyVectorJetBulkNorthWeightOrderGapSource
          s hs (centralExtent halfTime) time)) :=
  expectation_certificate_nonnegative w hw0 hw1 halfTime _
    (globalCayleyVectorJetBulkNorthWeightOrderGap_certificate
      s hs (centralExtent halfTime) time)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightOrder

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightOrder.bernoulliGap_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightOrder.globalCayleyNorthBernoulliGap_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightOrder.globalCayleyVectorJetNorthWeightOrderGap_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightOrder.globalCayleyVectorJetBulkNorthWeightOrderGap_certificate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightOrder.globalCayleyVectorJetBulkNorthWeightOrderGap_expectation_nonnegative
