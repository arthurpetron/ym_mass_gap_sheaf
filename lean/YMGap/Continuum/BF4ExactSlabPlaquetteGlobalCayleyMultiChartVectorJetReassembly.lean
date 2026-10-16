/-
# Lossless sixteen-chart reassembly of the global Cayley vector jet

For every Boolean four-link chart, the actual signed Cayley clearing is
identified on the unchanged ORIGINAL slab Haar carrier with
`2^66 * W_s^14 * V`.  Multiplication by the certificate-positive quotient
from the fourteenth-order subordinate partition changes this to
`2^66 * Omega_s * V`.  Summing all sixteen terms and using the exact
subordinate partition therefore reconstructs `2^66 * V` without a chart
loss.

This is a finite carrier identity.  It does not estimate a centered
remainder, compare to the FREE Gaussian law, remove a cutoff, construct a
continuum Hamiltonian, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartPowerPartition
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization
import YMGap.Continuum.SU2CharacterSquareIdentity

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

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
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeight
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4ExactSlabPlaquetteSignedCayleyExtraction
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2CharacterSquareIdentity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- The selected central-sign representative of the first oriented link. -/
def signedChartFaceQuaternion0
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternion :=
  signedChartQuaternion chart.south0
    (faceCayleyQuaternion0 extent face)

def signedChartFaceQuaternion1
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternion :=
  signedChartQuaternion chart.south1
    (faceCayleyQuaternion1 extent face)

def signedChartFaceQuaternion2
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternion :=
  signedChartQuaternion chart.south2
    (faceCayleyQuaternion2 extent face)

def signedChartFaceQuaternion3
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternion :=
  signedChartQuaternion chart.south3
    (faceCayleyQuaternion3 extent face)

/-- Ordered four-link word after the selected central signs. -/
def globalCayleySignedChartQuaternionWord
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (PolyQuaternion.mul
        (signedChartFaceQuaternion0 extent face chart)
        (signedChartFaceQuaternion1 extent face chart))
      (signedChartFaceQuaternion2 extent face chart))
    (signedChartFaceQuaternion3 extent face chart)

def polyQuaternionVectorJet (q : PolyQuaternion) : RatPoly :=
  polyAdd (polyMul q.iPart q.iPart)
    (polyAdd (polyMul q.jPart q.jPart) (polyMul q.kPart q.kPart))

/-- Vector norm of the signed chart word. -/
def globalCayleySignedChartVectorJet
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyQuaternionVectorJet
    (globalCayleySignedChartQuaternionWord extent face chart)

private def signedQuaternionExpr
    (south : Bool) (q : PolyQuaternionExpr) : PolyQuaternionExpr :=
  if south then
    ⟨.neg q.scalar, .neg q.iPart, .neg q.jPart, .neg q.kPart⟩
  else q

private def coeffEvalQuaternionExpr
    (environment : Nat → RatPoly) (q : PolyQuaternionExpr) : PolyQuaternion :=
  ⟨coeffEvalExpr environment q.scalar,
    coeffEvalExpr environment q.iPart,
    coeffEvalExpr environment q.jPart,
    coeffEvalExpr environment q.kPart⟩

private theorem coeffEvalQuaternionExpr_eqv_of_normalize_eq
    (environment : Nat → RatPoly) (left right : PolyQuaternionExpr)
    (hscalar : normalize left.scalar = normalize right.scalar)
    (hiPart : normalize left.iPart = normalize right.iPart)
    (hjPart : normalize left.jPart = normalize right.jPart)
    (hkPart : normalize left.kPart = normalize right.kPart) :
    PolyQuaternionCoeffEqv
      (coeffEvalQuaternionExpr environment left)
      (coeffEvalQuaternionExpr environment right) :=
  ⟨coeffEvalExpr_eqv_of_normalize_eq
      left.scalar right.scalar hscalar environment,
    coeffEvalExpr_eqv_of_normalize_eq
      left.iPart right.iPart hiPart environment,
    coeffEvalExpr_eqv_of_normalize_eq
      left.jPart right.jPart hjPart environment,
    coeffEvalExpr_eqv_of_normalize_eq
      left.kPart right.kPart hkPart environment⟩

private def twoQuaternionEnvironment
    (first second : PolyQuaternion) : Nat → RatPoly
  | 0 => first.scalar
  | 1 => first.iPart
  | 2 => first.jPart
  | 3 => first.kPart
  | 4 => second.scalar
  | 5 => second.iPart
  | 6 => second.jPart
  | _ => second.kPart

/-- Polynomial central signs multiply by Boolean xor. -/
theorem signedChartQuaternion_mul_coeff
    (south west : Bool) (first second : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul
        (signedChartQuaternion south first)
        (signedChartQuaternion west second))
      (signedChartQuaternion (Bool.xor south west)
        (PolyQuaternion.mul first second)) := by
  let environment := twoQuaternionEnvironment first second
  let firstExpression := PolyQuaternionExpr.coordinate 0
  let secondExpression := PolyQuaternionExpr.coordinate 4
  let left := PolyQuaternionExpr.mul
    (signedQuaternionExpr south firstExpression)
    (signedQuaternionExpr west secondExpression)
  let right := signedQuaternionExpr (Bool.xor south west)
    (PolyQuaternionExpr.mul firstExpression secondExpression)
  have h := coeffEvalQuaternionExpr_eqv_of_normalize_eq
    environment left right
    (by cases south <;> cases west <;> decide)
    (by cases south <;> cases west <;> decide)
    (by cases south <;> cases west <;> decide)
    (by cases south <;> cases west <;> decide)
  cases south <;> cases west <;>
    simpa [environment, firstExpression, secondExpression, left, right,
      twoQuaternionEnvironment, signedQuaternionExpr,
      signedChartQuaternion, coeffEvalQuaternionExpr,
      PolyQuaternionExpr.coordinate, PolyQuaternionExpr.mul,
      coeffEvalExpr, PolyQuaternion.mul] using h

private theorem signedChartQuaternion_congr
    (south : Bool) {first second : PolyQuaternion}
    (h : PolyQuaternionCoeffEqv first second) :
    PolyQuaternionCoeffEqv
      (signedChartQuaternion south first)
      (signedChartQuaternion south second) := by
  cases south
  · exact h
  · exact ⟨RatPolyCoeffEqv.neg h.scalar,
      RatPolyCoeffEqv.neg h.iPart,
      RatPolyCoeffEqv.neg h.jPart,
      RatPolyCoeffEqv.neg h.kPart⟩

/-- The four selected link signs combine to the chart's plaquette parity. -/
theorem globalCayleySignedChartQuaternionWord_coeff_sector
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternionCoeffEqv
      (globalCayleySignedChartQuaternionWord extent face chart)
      (signedChartQuaternion chart.sector
        (faceCayleyQuaternionWord extent face)) := by
  let q0 := faceCayleyQuaternion0 extent face
  let q1 := faceCayleyQuaternion1 extent face
  let q2 := faceCayleyQuaternion2 extent face
  let q3 := faceCayleyQuaternion3 extent face
  have h01 := signedChartQuaternion_mul_coeff
    chart.south0 chart.south1 q0 q1
  have h012 :=
    (PolyQuaternionCoeffEqv.mul h01
      (PolyQuaternionCoeffEqv.refl
        (signedChartQuaternion chart.south2 q2))).trans
      (signedChartQuaternion_mul_coeff
        (Bool.xor chart.south0 chart.south1) chart.south2
        (PolyQuaternion.mul q0 q1) q2)
  have h0123 :=
    (PolyQuaternionCoeffEqv.mul h012
      (PolyQuaternionCoeffEqv.refl
        (signedChartQuaternion chart.south3 q3))).trans
      (signedChartQuaternion_mul_coeff
        (Bool.xor (Bool.xor chart.south0 chart.south1) chart.south2)
        chart.south3
        (PolyQuaternion.mul (PolyQuaternion.mul q0 q1) q2) q3)
  simpa [q0, q1, q2, q3, globalCayleySignedChartQuaternionWord,
    signedChartFaceQuaternion0, signedChartFaceQuaternion1,
    signedChartFaceQuaternion2, signedChartFaceQuaternion3,
    FourCayleyChart.sector, plaquetteSign, faceCayleyQuaternionWord] using
      h0123

private theorem polyQuaternionVectorJet_congr
    {first second : PolyQuaternion}
    (h : PolyQuaternionCoeffEqv first second) :
    RatPolyCoeffEqv
      (polyQuaternionVectorJet first)
      (polyQuaternionVectorJet second) :=
  (h.iPart.mul h.iPart).add
    ((h.jPart.mul h.jPart).add (h.kPart.mul h.kPart))

private theorem polyQuaternionVectorJet_signed
    (south : Bool) (q : PolyQuaternion) :
    RatPolyCoeffEqv
      (polyQuaternionVectorJet (signedChartQuaternion south q))
      (polyQuaternionVectorJet q) := by
  cases south
  · exact RatPolyCoeffEqv.refl _
  · unfold polyQuaternionVectorJet signedChartQuaternion
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.neg (.var 0)) (.neg (.var 0)))
        (.add (.mul (.neg (.var 1)) (.neg (.var 1)))
          (.mul (.neg (.var 2)) (.neg (.var 2)))))
      (.add (.mul (.var 0) (.var 0))
        (.add (.mul (.var 1) (.var 1))
          (.mul (.var 2) (.var 2))))
      (by decide)
      (fun | 0 => q.iPart | 1 => q.jPart | _ => q.kPart)

/-- Central chart parity disappears from the squared vector jet. -/
theorem globalCayleySignedChartVectorJet_coeff_original
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    RatPolyCoeffEqv
      (globalCayleySignedChartVectorJet extent face chart)
      (globalPlaquetteVectorJet extent face) := by
  have hsector := globalCayleySignedChartQuaternionWord_coeff_sector
    extent face chart
  have hword :=
    correctedSlabPlaquettePolynomial_coeff_faceCayleyQuaternionWord
      extent face
  exact (polyQuaternionVectorJet_congr hsector).trans
    ((polyQuaternionVectorJet_signed chart.sector
      (faceCayleyQuaternionWord extent face)).trans
        ((polyQuaternionVectorJet_congr hword.symm).trans
          (RatPolyCoeffEqv.refl _)))

def signedChartComplement0
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  cayleyComplement0Polynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

def signedChartComplement1
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  cayleyComplement1Polynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

def signedChartComplement2
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  cayleyComplement2Polynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

def signedChartComplement3
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  cayleyComplement3Polynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

/-- Actual product of the four signed Cayley clearing scales. -/
def globalCayleySignedChartScaleProduct
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  clearedCayleyScaleProduct
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

/-- Unit-norm-reduced product of the four signed north factors. -/
def globalCayleySignedChartNorthFactorProduct
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (polyMul
      (polyMul
        (northCayleyFactorPolynomial
          (signedChartFaceQuaternion0 extent face chart)
          (signedChartComplement0 extent face chart))
        (northCayleyFactorPolynomial
          (signedChartFaceQuaternion1 extent face chart)
          (signedChartComplement1 extent face chart)))
      (northCayleyFactorPolynomial
        (signedChartFaceQuaternion2 extent face chart)
        (signedChartComplement2 extent face chart)))
    (northCayleyFactorPolynomial
      (signedChartFaceQuaternion3 extent face chart)
      (signedChartComplement3 extent face chart))

/-- The actual signed clearing scale reduces to the signed north-factor
product on the unchanged ORIGINAL Haar carrier. -/
theorem globalCayleySignedChartScaleProduct_carrier_northFactor
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartScaleProduct extent face chart)
      (globalCayleySignedChartNorthFactorProduct extent face chart) := by
  let q0 := faceCayleyQuaternion0 extent face
  let q1 := faceCayleyQuaternion1 extent face
  let q2 := faceCayleyQuaternion2 extent face
  let q3 := faceCayleyQuaternion3 extent face
  let n0 := signedChartQuaternion chart.south0 q0
  let n1 := signedChartQuaternion chart.south1 q1
  let n2 := signedChartQuaternion chart.south2 q2
  let n3 := signedChartQuaternion chart.south3 q3
  let c0 := cayleyComplement0Polynomial n0 n1 n2 n3
  let c1 := cayleyComplement1Polynomial n0 n1 n2 n3
  let c2 := cayleyComplement2Polynomial n0 n1 n2 n3
  let c3 := cayleyComplement3Polynomial n0 n1 n2 n3
  have h0 := clearedCayleyFactorPolynomial_carrier_north n0 c0
    (haarNorm_signedChartQuaternion chart.south0
      (haarNorm_orientedCorrectedSlabLinkPolynomial extent
        (faceCayleyEntry0 face)))
  have h1 := clearedCayleyFactorPolynomial_carrier_north n1 c1
    (haarNorm_signedChartQuaternion chart.south1
      (haarNorm_orientedCorrectedSlabLinkPolynomial extent
        (faceCayleyEntry1 face)))
  have h2 := clearedCayleyFactorPolynomial_carrier_north n2 c2
    (haarNorm_signedChartQuaternion chart.south2
      (haarNorm_orientedCorrectedSlabLinkPolynomial extent
        (faceCayleyEntry2 face)))
  have h3 := clearedCayleyFactorPolynomial_carrier_north n3 c3
    (haarNorm_signedChartQuaternion chart.south3
      (haarNorm_orientedCorrectedSlabLinkPolynomial extent
        (faceCayleyEntry3 face)))
  simpa [q0, q1, q2, q3, n0, n1, n2, n3, c0, c1, c2, c3,
    globalCayleySignedChartScaleProduct,
    globalCayleySignedChartNorthFactorProduct,
    signedChartFaceQuaternion0, signedChartFaceQuaternion1,
    signedChartFaceQuaternion2, signedChartFaceQuaternion3,
    signedChartComplement0, signedChartComplement1,
    signedChartComplement2, signedChartComplement3,
    clearedCayleyScaleProduct] using
      (HaarCarrierEqv.mul
        (HaarCarrierEqv.mul (HaarCarrierEqv.mul h0 h1) h2) h3)

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private def eComplement0 : PE := (.var 1 * .var 2) * .var 3
private def eComplement1 : PE := (.var 0 * .var 2) * .var 3
private def eComplement2 : PE := (.var 0 * .var 1) * .var 3
private def eComplement3 : PE := (.var 0 * .var 1) * .var 2

private def eNorthFactor (index : Nat) (complement : PE) : PE :=
  (2 * .var index) * (complement * complement)

private def eNorthFactorProduct : PE :=
  ((eNorthFactor 0 eComplement0 * eNorthFactor 1 eComplement1) *
      eNorthFactor 2 eComplement2) *
    eNorthFactor 3 eComplement3

private def eDoubleBase : Nat → PE
  | 0 => 2 * .var 0
  | 1 => 2 * .var 1
  | 2 => 2 * .var 2
  | 3 => 2 * .var 3
  | _ => 0

private def eBaseProduct : PE :=
  (.var 0 * .var 1) * (.var 2 * .var 3)

private def eScaledBasePower7 : PE :=
  .const (2 ^ 32) * .pow eBaseProduct 7

private theorem northFactorProduct_normalized :
    normalize (substE eDoubleBase eNorthFactorProduct) =
      normalize eScaledBasePower7 := by
  decide

private def signedChartDenominatorEnvironment
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    Nat → RatPoly
  | 0 => cayleyChartDenominatorPolynomial
      (signedChartFaceQuaternion0 extent face chart)
  | 1 => cayleyChartDenominatorPolynomial
      (signedChartFaceQuaternion1 extent face chart)
  | 2 => cayleyChartDenominatorPolynomial
      (signedChartFaceQuaternion2 extent face chart)
  | 3 => cayleyChartDenominatorPolynomial
      (signedChartFaceQuaternion3 extent face chart)
  | _ => polyZero

private def signedChartBaseEnvironment
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    Nat → RatPoly
  | 0 => cayleyChartBasePolynomial chart.south0
      (faceCayleyQuaternion0 extent face)
  | 1 => cayleyChartBasePolynomial chart.south1
      (faceCayleyQuaternion1 extent face)
  | 2 => cayleyChartBasePolynomial chart.south2
      (faceCayleyQuaternion2 extent face)
  | 3 => cayleyChartBasePolynomial chart.south3
      (faceCayleyQuaternion3 extent face)
  | _ => polyZero

private theorem polyConst_coeff_smul (coefficient : Q') :
    RatPolyCoeffEqv (polyConst coefficient)
      (polySmul coefficient polyOne) := by
  intro weight
  change coefficient * weight [] + 0 ≈
    (coefficient * 1) * weight [] + 0
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv coefficient)))
    (Q'.eqv_refl 0)

/-- The signed north-factor product is exactly `2^32 * W_s^7`. -/
theorem globalCayleySignedChartNorthFactorProduct_coeff_power7
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    RatPolyCoeffEqv
      (globalCayleySignedChartNorthFactorProduct extent face chart)
      (polyMul (polySmul (Q'.ofInt (2 ^ 32)) polyOne)
        (coeffPolyPow
          (globalCayleyChartWeightPolynomial extent face chart) 7)) := by
  let n0 := signedChartFaceQuaternion0 extent face chart
  let n1 := signedChartFaceQuaternion1 extent face chart
  let n2 := signedChartFaceQuaternion2 extent face chart
  let n3 := signedChartFaceQuaternion3 extent face chart
  let c0 := signedChartComplement0 extent face chart
  let c1 := signedChartComplement1 extent face chart
  let c2 := signedChartComplement2 extent face chart
  let c3 := signedChartComplement3 extent face chart
  have h0 := northCayleyFactorPolynomial_coeff_formula n0 c0
  have h1 := northCayleyFactorPolynomial_coeff_formula n1 c1
  have h2 := northCayleyFactorPolynomial_coeff_formula n2 c2
  have h3 := northCayleyFactorPolynomial_coeff_formula n3 c3
  have hexpanded : RatPolyCoeffEqv
      (globalCayleySignedChartNorthFactorProduct extent face chart)
      (coeffEvalExpr
        (signedChartDenominatorEnvironment extent face chart)
        eNorthFactorProduct) := by
    simpa [n0, n1, n2, n3, c0, c1, c2, c3,
      globalCayleySignedChartNorthFactorProduct,
      signedChartDenominatorEnvironment,
      eNorthFactorProduct, eNorthFactor,
      eComplement0, eComplement1, eComplement2, eComplement3,
      signedChartComplement0, signedChartComplement1,
      signedChartComplement2, signedChartComplement3,
      cayleyComplement0Polynomial, cayleyComplement1Polynomial,
      cayleyComplement2Polynomial, cayleyComplement3Polynomial] using
        (RatPolyCoeffEqv.mul
          (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.mul h0 h1) h2) h3)
  have hdouble : ∀ index,
      RatPolyCoeffEqv
        (signedChartDenominatorEnvironment extent face chart index)
        (coeffEvalExpr
          (signedChartBaseEnvironment extent face chart)
          (eDoubleBase index)) := by
    intro index
    rcases index with _ | index
    · simpa [signedChartDenominatorEnvironment,
        signedChartBaseEnvironment, eDoubleBase,
        cayleyChartBasePolynomial,
        signedChartFaceQuaternion0] using
          (cayleyChartDenominatorPolynomial_coeff_double_base n0)
    rcases index with _ | index
    · simpa [signedChartDenominatorEnvironment,
        signedChartBaseEnvironment, eDoubleBase,
        cayleyChartBasePolynomial,
        signedChartFaceQuaternion1] using
          (cayleyChartDenominatorPolynomial_coeff_double_base n1)
    rcases index with _ | index
    · simpa [signedChartDenominatorEnvironment,
        signedChartBaseEnvironment, eDoubleBase,
        cayleyChartBasePolynomial,
        signedChartFaceQuaternion2] using
          (cayleyChartDenominatorPolynomial_coeff_double_base n2)
    rcases index with _ | index
    · simpa [signedChartDenominatorEnvironment,
        signedChartBaseEnvironment, eDoubleBase,
        cayleyChartBasePolynomial,
        signedChartFaceQuaternion3] using
          (cayleyChartDenominatorPolynomial_coeff_double_base n3)
    · simpa [signedChartDenominatorEnvironment,
        signedChartBaseEnvironment, eDoubleBase] using
          (RatPolyCoeffEqv.zero_smul polyOne).symm
  have hnormalized := transport eDoubleBase hdouble eNorthFactorProduct
    eScaledBasePower7 northFactorProduct_normalized
  refine hexpanded.trans ?_
  simpa [signedChartBaseEnvironment, eScaledBasePower7, eBaseProduct,
    globalCayleyChartWeightPolynomial] using hnormalized

private def eSingleScaledBasePower7 : PE :=
  .const (2 ^ 32) * .pow (.var 0) 7

private def eScaledVectorWeightFromPower7 : PE :=
  4 * (eSingleScaledBasePower7 * eSingleScaledBasePower7)

private def eScaledBasePower14 : PE :=
  .const (2 ^ 66) * .pow (.var 0) 14

private theorem scaledVectorWeight_normalized :
    normalize eScaledVectorWeightFromPower7 =
      normalize eScaledBasePower14 := by
  decide

private def singleChartWeightEnvironment
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    Nat → RatPoly
  | 0 => globalCayleyChartWeightPolynomial extent face chart
  | _ => polyZero

/-- Squaring the signed factor normalization gives
`2^66 * W_s^14`. -/
theorem globalCayleySignedChartClearedWeight_coeff_power14
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    RatPolyCoeffEqv
      (polyMul (polyConst 4)
        (polyMul
          (globalCayleySignedChartNorthFactorProduct extent face chart)
          (globalCayleySignedChartNorthFactorProduct extent face chart)))
      (polyMul (polySmul (Q'.ofInt (2 ^ 66)) polyOne)
        (coeffPolyPow
          (globalCayleyChartWeightPolynomial extent face chart) 14)) := by
  have hfactor := globalCayleySignedChartNorthFactorProduct_coeff_power7
    extent face chart
  have hexpanded : RatPolyCoeffEqv
      (polyMul (polyConst 4)
        (polyMul
          (globalCayleySignedChartNorthFactorProduct extent face chart)
          (globalCayleySignedChartNorthFactorProduct extent face chart)))
      (coeffEvalExpr (singleChartWeightEnvironment extent face chart)
        eScaledVectorWeightFromPower7) := by
    simpa [singleChartWeightEnvironment, eScaledVectorWeightFromPower7,
      eSingleScaledBasePower7] using
        (RatPolyCoeffEqv.mul (polyConst_coeff_smul 4)
          (RatPolyCoeffEqv.mul hfactor hfactor))
  refine hexpanded.trans ?_
  simpa [singleChartWeightEnvironment, eScaledBasePower14] using
    (coeffEvalExpr_eqv_of_normalize_eq eScaledVectorWeightFromPower7
      eScaledBasePower14 scaledVectorWeight_normalized
      (singleChartWeightEnvironment extent face chart))

/-- Actual signed-chart denominator-square-cleared vector jet. -/
def globalCayleySignedChartVectorJetClearedPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (polyMul (polyConst 4)
      (polyMul
        (globalCayleySignedChartScaleProduct extent face chart)
        (globalCayleySignedChartScaleProduct extent face chart)))
    (globalCayleySignedChartVectorJet extent face chart)

/-- Every actual signed-chart clearing has the common physical vector jet
and the exact normalized factor `2^66 * W_s^14`. -/
theorem globalCayleySignedChartVectorJetCleared_carrier_power14
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartVectorJetClearedPolynomial extent face chart)
      (polyMul
        (polyMul (polySmul (Q'.ofInt (2 ^ 66)) polyOne)
          (coeffPolyPow
            (globalCayleyChartWeightPolynomial extent face chart) 14))
        (globalPlaquetteVectorJet extent face)) := by
  have hscale := globalCayleySignedChartScaleProduct_carrier_northFactor
    extent face chart
  have hweight : HaarCarrierEqv
      (boundaryCompleteSlabLinks extent).length
      (polyMul (polyConst 4)
        (polyMul
          (globalCayleySignedChartScaleProduct extent face chart)
          (globalCayleySignedChartScaleProduct extent face chart)))
      (polyMul (polySmul (Q'.ofInt (2 ^ 66)) polyOne)
        (coeffPolyPow
          (globalCayleyChartWeightPolynomial extent face chart) 14)) :=
    (HaarCarrierEqv.mul
      (HaarCarrierEqv.refl _ (polyConst 4))
      (HaarCarrierEqv.mul hscale hscale)).trans
        (RatPolyCoeffEqv.haarCarrier
          (globalCayleySignedChartClearedWeight_coeff_power14
            extent face chart))
  unfold globalCayleySignedChartVectorJetClearedPolynomial
  exact HaarCarrierEqv.mul hweight
    (RatPolyCoeffEqv.haarCarrier
      (globalCayleySignedChartVectorJet_coeff_original extent face chart))

/-- Actual chartwise clearing multiplied by the positive quotient which
extracts the subordinate partition weight. -/
def globalCayleySignedChartReassemblyTerm
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (globalCayleySubordinateChartQuotientPolynomial extent face chart)
    (globalCayleySignedChartVectorJetClearedPolynomial extent face chart)

def globalCayleySignedChartReassemblyPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  finitePolySum
    (globalCayleySignedChartReassemblyTerm extent face)
    fourCayleyChartTable

private def globalCayleySignedChartNormalizedTerm
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (polyMul (polySmul (Q'.ofInt (2 ^ 66)) polyOne)
      (globalCayleySubordinateChartWeightPolynomial extent face chart))
    (globalPlaquetteVectorJet extent face)

private theorem chartReassemblyTerm_carrier_normalized
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartReassemblyTerm extent face chart)
      (globalCayleySignedChartNormalizedTerm extent face chart) := by
  let quotient := globalCayleySubordinateChartQuotientPolynomial
    extent face chart
  let weightPower := coeffPolyPow
    (globalCayleyChartWeightPolynomial extent face chart) 14
  let subordinateWeight := globalCayleySubordinateChartWeightPolynomial
    extent face chart
  let vectorJet := globalPlaquetteVectorJet extent face
  let scale := polySmul (Q'.ofInt (2 ^ 66)) polyOne
  have hcleared := globalCayleySignedChartVectorJetCleared_carrier_power14
    extent face chart
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleySignedChartVectorJetClearedPolynomial extent face chart)
    (polyMul (polyMul scale weightPower) vectorJet) at hcleared
  have hfactor :=
    globalCayleySubordinateChartWeight_coeff_power14_quotient
      extent face chart
  change RatPolyCoeffEqv subordinateWeight
    (polyMul weightPower quotient) at hfactor
  have hring : RatPolyCoeffEqv
      (polyMul quotient (polyMul (polyMul scale weightPower) vectorJet))
      (polyMul (polyMul scale subordinateWeight) vectorJet) := by
    have hshape := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (.mul (.mul (.var 1) (.mul (.var 2) (.var 0))) (.var 3))
      (by decide)
      (fun | 0 => quotient | 1 => scale | 2 => weightPower | _ => vectorJet)
    exact hshape.trans
      ((RatPolyCoeffEqv.refl scale).mul hfactor.symm |>.mul
        (RatPolyCoeffEqv.refl vectorJet))
  unfold globalCayleySignedChartReassemblyTerm
  exact (HaarCarrierEqv.mul
    (HaarCarrierEqv.refl _ quotient) hcleared).trans
      (RatPolyCoeffEqv.haarCarrier hring)

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

private theorem finiteSum_scaled_partition_coeff
    (scale vectorJet : RatPoly) (weight : FourCayleyChart → RatPoly) :
    ∀ items,
      RatPolyCoeffEqv
        (finitePolySum
          (fun chart => polyMul (polyMul scale (weight chart)) vectorJet)
          items)
        (polyMul scale
          (polyMul (finitePolySum weight items) vectorJet))
  | [] => by
      change RatPolyCoeffEqv polyZero
        (polyMul scale (polyMul polyZero vectorJet))
      exact ((RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl scale)
        (RatPolyCoeffEqv.mul_zero_left vectorJet)).trans
          (RatPolyCoeffEqv.mul_zero_right scale)).symm
  | chart :: items => by
      have hrest := finiteSum_scaled_partition_coeff
        scale vectorJet weight items
      have hregroup := coeffEvalExpr_eqv_of_normalize_eq
        (.add
          (.mul (.mul (.var 0) (.var 1)) (.var 3))
          (.mul (.var 0) (.mul (.var 2) (.var 3))))
        (.mul (.var 0) (.mul (.add (.var 1) (.var 2)) (.var 3)))
        (by decide)
        (fun index => match index with
          | 0 => scale
          | 1 => weight chart
          | 2 => finitePolySum weight items
          | _ => vectorJet)
      exact ((RatPolyCoeffEqv.refl _).add hrest).trans hregroup

private theorem normalizedReassembly_coeff_identityScaled
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (finitePolySum
        (globalCayleySignedChartNormalizedTerm extent face)
        fourCayleyChartTable)
      (polyMul (polySmul (Q'.ofInt (2 ^ 66)) polyOne)
        (globalPlaquetteVectorJet extent face)) := by
  let scale := polySmul (Q'.ofInt (2 ^ 66)) polyOne
  let vectorJet := globalPlaquetteVectorJet extent face
  let weight := globalCayleySubordinateChartWeightPolynomial extent face
  have hfactor := finiteSum_scaled_partition_coeff
    scale vectorJet weight fourCayleyChartTable
  have hpartition := globalCayleySubordinateChartPartition_coeff_one
    extent face
  change RatPolyCoeffEqv (finitePolySum
    (fun chart => polyMul (polyMul scale (weight chart)) vectorJet)
    fourCayleyChartTable) (polyMul scale vectorJet)
  exact hfactor.trans
    (((RatPolyCoeffEqv.refl scale).mul
      ((hpartition.mul (RatPolyCoeffEqv.refl vectorJet)).trans
        (RatPolyCoeffEqv.one_mul vectorJet))).trans
          (RatPolyCoeffEqv.refl _))

/-- The sixteen actual signed-chart clearings, each multiplied by its
positive subordinate quotient, reconstruct the identity-scaled physical
vector jet on the unchanged ORIGINAL Haar carrier without chart loss. -/
theorem globalCayleySignedChartReassembly_carrier_identityScaled
    (extent : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartReassemblyPolynomial extent face)
      (polyMul (polySmul (Q'.ofInt (2 ^ 66)) polyOne)
        (globalPlaquetteVectorJet extent face)) := by
  have hsum := finiteSum_carrier
    (boundaryCompleteSlabLinks extent).length
    (globalCayleySignedChartReassemblyTerm extent face)
    (globalCayleySignedChartNormalizedTerm extent face)
    fourCayleyChartTable
    (fun chart _ => chartReassemblyTerm_carrier_normalized
      extent face chart)
  exact hsum.trans (RatPolyCoeffEqv.haarCarrier
    (normalizedReassembly_coeff_identityScaled extent face))

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly.signedChartQuaternion_mul_coeff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly.globalCayleySignedChartQuaternionWord_coeff_sector
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly.globalCayleySignedChartVectorJet_coeff_original
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly.globalCayleySignedChartScaleProduct_carrier_northFactor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly.globalCayleySignedChartNorthFactorProduct_coeff_power7
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly.globalCayleySignedChartClearedWeight_coeff_power14
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly.globalCayleySignedChartVectorJetCleared_carrier_power14
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly.globalCayleySignedChartReassembly_carrier_identityScaled
