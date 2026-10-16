/-
# Exact normalization of the global north-chart weight

The four local north factors from the denominator-cleared plaquette response
are normalized here by the actual scalar kernel bases `(1+r)/2`.  The full
factor product is coefficientwise `2^32` times the seventh power of their
four-link product.  Evaluation on the ORIGINAL oriented slab links is exactly
the existing rational quaternion kernel product, hence belongs to `[0,1]`.

This is a finite polynomial identity and pointwise unit-quaternion bound.  It
does not divide by the north weight, which may vanish at the south pole, and
it does not yet pay the resulting southern sector in the centered response.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeight
import YMGap.Continuum.SU2CharacterSquareIdentity
import YMGap.Continuum.SU2QuaternionWilsonWeightSOS
import YMGap.Continuum.R1CornerAtoms
import YMGap.RepTheory.RationalQuaternionFourKernelProduct

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half)
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.RepTheory.RationalQuaternionFourKernelProduct
  (base product product_bounds)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabPlaquetteDeficit
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeight
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2CharacterSquareIdentity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
  (evalRatPoly_one evalRatPoly_smul)
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
  (ratWeightedSum)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.R1CornerAtoms (oneSub_qpow_le)

local infix:50 " ≈ " => Q'.eqv

private theorem ac {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a + c ≈ b + d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
    (Q'.add_eqv_congr_left _ _ _ k)

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a * c ≈ b * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- The normalized scalar north base `(1 + scalar(q)) / 2`. -/
def northCayleyBasePolynomial (q : PolyQuaternion) : RatPoly :=
  polySmul half (cayleyChartDenominatorPolynomial q)

/-- Balanced product of the four normalized north bases on one plaquette. -/
def globalCayleyNorthBaseProduct
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul
    (polyMul
      (northCayleyBasePolynomial (faceCayleyQuaternion0 extent face))
      (northCayleyBasePolynomial (faceCayleyQuaternion1 extent face)))
    (polyMul
      (northCayleyBasePolynomial (faceCayleyQuaternion2 extent face))
      (northCayleyBasePolynomial (faceCayleyQuaternion3 extent face)))

/-- Literal polynomial representative of `2^32 * P^7`, where `P` is the
four-link normalized north-base product. -/
def globalCayleyNorthScaledBasePower7
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul (polySmul (Q'.ofInt (2 ^ 32)) polyOne)
    (coeffPolyPow (globalCayleyNorthBaseProduct extent face) 7)

/-- Literal polynomial representative of the cleared vector-jet weight
`2^66 * P^14`. -/
def globalCayleyNorthBasePower14
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  coeffPolyPow (globalCayleyNorthBaseProduct extent face) 14

def globalCayleyNorthScaledBasePower14
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  polyMul (polySmul (Q'.ofInt (2 ^ 66)) polyOne)
    (globalCayleyNorthBasePower14 extent face)

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

private def eSingleScaledBasePower7 : PE :=
  .const (2 ^ 32) * .pow (.var 0) 7

private def eScaledVectorWeightFromPower7 : PE :=
  4 * (eSingleScaledBasePower7 * eSingleScaledBasePower7)

private def eScaledBasePower14 : PE :=
  .const (2 ^ 66) * .pow (.var 0) 14

set_option maxHeartbeats 2000000 in
private theorem northFactorProduct_normalized :
    normalize (substE eDoubleBase eNorthFactorProduct) =
      normalize eScaledBasePower7 := by
  decide

private def chartEnvironment
    (extent : Nat) (face : Z4Plaq) : Nat → RatPoly
  | 0 => cayleyChartDenominatorPolynomial (faceCayleyQuaternion0 extent face)
  | 1 => cayleyChartDenominatorPolynomial (faceCayleyQuaternion1 extent face)
  | 2 => cayleyChartDenominatorPolynomial (faceCayleyQuaternion2 extent face)
  | 3 => cayleyChartDenominatorPolynomial (faceCayleyQuaternion3 extent face)
  | _ => polyZero

private def baseEnvironment
    (extent : Nat) (face : Z4Plaq) : Nat → RatPoly
  | 0 => northCayleyBasePolynomial (faceCayleyQuaternion0 extent face)
  | 1 => northCayleyBasePolynomial (faceCayleyQuaternion1 extent face)
  | 2 => northCayleyBasePolynomial (faceCayleyQuaternion2 extent face)
  | 3 => northCayleyBasePolynomial (faceCayleyQuaternion3 extent face)
  | _ => polyZero

private def singleBaseEnvironment
    (extent : Nat) (face : Z4Plaq) : Nat → RatPoly
  | 0 => globalCayleyNorthBaseProduct extent face
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

/-- Each chart denominator is coefficientwise twice its normalized base. -/
theorem cayleyChartDenominatorPolynomial_coeff_double_base
    (q : PolyQuaternion) :
    RatPolyCoeffEqv
      (cayleyChartDenominatorPolynomial q)
      (polyMul (polySmul 2 polyOne) (northCayleyBasePolynomial q)) := by
  have hscaled : RatPolyCoeffEqv
      (polySmul 2 (northCayleyBasePolynomial q))
      (cayleyChartDenominatorPolynomial q) := by
    refine (RatPolyCoeffEqv.smul_assoc 2 half
      (cayleyChartDenominatorPolynomial q)).trans ?_
    exact (RatPolyCoeffEqv.smul_coefficient
      (by decide : (2 : Q') * half ≈ 1)
      (cayleyChartDenominatorPolynomial q)).trans
        (RatPolyCoeffEqv.one_smul (cayleyChartDenominatorPolynomial q))
  have hconstant : RatPolyCoeffEqv
      (polyMul (polySmul 2 polyOne) (northCayleyBasePolynomial q))
      (polySmul 2 (northCayleyBasePolynomial q)) :=
    (RatPolyCoeffEqv.polyMul_smul_left 2 polyOne
      (northCayleyBasePolynomial q)).trans
      ((RatPolyCoeffEqv.one_mul (northCayleyBasePolynomial q)).smul 2)
  exact hscaled.symm.trans hconstant.symm

set_option maxHeartbeats 2000000 in
/-- Exact coefficient normalization of the full four-factor north weight. -/
theorem globalCayleyNorthFactorProduct_coeff_scaledBasePower7
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (globalCayleyNorthFactorProduct extent face)
      (globalCayleyNorthScaledBasePower7 extent face) := by
  let q0 := faceCayleyQuaternion0 extent face
  let q1 := faceCayleyQuaternion1 extent face
  let q2 := faceCayleyQuaternion2 extent face
  let q3 := faceCayleyQuaternion3 extent face
  let c0 := faceCayleyComplement0 extent face
  let c1 := faceCayleyComplement1 extent face
  let c2 := faceCayleyComplement2 extent face
  let c3 := faceCayleyComplement3 extent face
  have h0 := northCayleyFactorPolynomial_coeff_formula q0 c0
  have h1 := northCayleyFactorPolynomial_coeff_formula q1 c1
  have h2 := northCayleyFactorPolynomial_coeff_formula q2 c2
  have h3 := northCayleyFactorPolynomial_coeff_formula q3 c3
  have hexpanded : RatPolyCoeffEqv
      (globalCayleyNorthFactorProduct extent face)
      (coeffEvalExpr (chartEnvironment extent face) eNorthFactorProduct) := by
    simpa [q0, q1, q2, q3, c0, c1, c2, c3,
      globalCayleyNorthFactorProduct, chartEnvironment, eNorthFactorProduct,
      eNorthFactor, eComplement0, eComplement1, eComplement2, eComplement3,
      faceCayleyComplement0, faceCayleyComplement1, faceCayleyComplement2,
      faceCayleyComplement3, cayleyComplement0Polynomial,
      cayleyComplement1Polynomial, cayleyComplement2Polynomial,
      cayleyComplement3Polynomial] using
        (RatPolyCoeffEqv.mul
          (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.mul h0 h1) h2) h3)
  have hdouble : ∀ index,
      RatPolyCoeffEqv (chartEnvironment extent face index)
        (coeffEvalExpr (baseEnvironment extent face) (eDoubleBase index)) := by
    intro index
    rcases index with _ | index
    · simpa [chartEnvironment, baseEnvironment, eDoubleBase] using
        (cayleyChartDenominatorPolynomial_coeff_double_base q0)
    rcases index with _ | index
    · simpa [chartEnvironment, baseEnvironment, eDoubleBase] using
        (cayleyChartDenominatorPolynomial_coeff_double_base q1)
    rcases index with _ | index
    · simpa [chartEnvironment, baseEnvironment, eDoubleBase] using
        (cayleyChartDenominatorPolynomial_coeff_double_base q2)
    rcases index with _ | index
    · simpa [chartEnvironment, baseEnvironment, eDoubleBase] using
        (cayleyChartDenominatorPolynomial_coeff_double_base q3)
    · simpa [chartEnvironment, baseEnvironment, eDoubleBase] using
        (RatPolyCoeffEqv.zero_smul polyOne).symm
  have hnormalized := transport eDoubleBase hdouble eNorthFactorProduct
    eScaledBasePower7 northFactorProduct_normalized
  refine hexpanded.trans ?_
  simpa [baseEnvironment, eScaledBasePower7, eBaseProduct,
    globalCayleyNorthScaledBasePower7, globalCayleyNorthBaseProduct] using
      hnormalized

private theorem scaledVectorWeight_normalized :
    normalize eScaledVectorWeightFromPower7 =
      normalize eScaledBasePower14 := by
  decide

set_option maxHeartbeats 2000000 in
/-- Squaring the exact denominator normalization and restoring the literal
vector-jet factor `4` gives exactly `2^66 * P^14`. -/
theorem globalCayleyNorthClearedWeight_coeff_scaledBasePower14
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv
      (polyMul (polyConst 4)
        (polyMul
          (globalCayleyNorthFactorProduct extent face)
          (globalCayleyNorthFactorProduct extent face)))
      (globalCayleyNorthScaledBasePower14 extent face) := by
  have hfactor :=
    globalCayleyNorthFactorProduct_coeff_scaledBasePower7 extent face
  have hexpanded : RatPolyCoeffEqv
      (polyMul (polyConst 4)
        (polyMul
          (globalCayleyNorthFactorProduct extent face)
          (globalCayleyNorthFactorProduct extent face)))
      (coeffEvalExpr (singleBaseEnvironment extent face)
        eScaledVectorWeightFromPower7) := by
    simpa [singleBaseEnvironment, eScaledVectorWeightFromPower7,
      eSingleScaledBasePower7, globalCayleyNorthScaledBasePower7] using
        (RatPolyCoeffEqv.mul (polyConst_coeff_smul 4)
          (RatPolyCoeffEqv.mul hfactor hfactor))
  refine hexpanded.trans ?_
  simpa [singleBaseEnvironment, eScaledBasePower14,
    globalCayleyNorthScaledBasePower14] using
      (coeffEvalExpr_eqv_of_normalize_eq eScaledVectorWeightFromPower7
        eScaledBasePower14 scaledVectorWeight_normalized
        (singleBaseEnvironment extent face))

/-- The actual cleared vector jet is the pure ORIGINAL vector jet multiplied
by the explicit normalized north weight `2^66 * P^14` on the slab Haar
carrier. -/
theorem globalCayleyVectorJetClearedPolynomial_carrier_scaledBasePower14
    (extent : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyVectorJetClearedPolynomial extent face)
      (polyMul (globalCayleyNorthScaledBasePower14 extent face)
        (globalPlaquetteVectorJet extent face)) := by
  have hcleared :=
    globalCayleyVectorJetClearedPolynomial_carrier_northWeight extent face
  have hweight : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyMul (polyConst 4)
        (polyMul
          (globalCayleyNorthFactorProduct extent face)
          (globalCayleyNorthFactorProduct extent face)))
      (globalCayleyNorthScaledBasePower14 extent face) :=
    RatPolyCoeffEqv.haarCarrier
      (globalCayleyNorthClearedWeight_coeff_scaledBasePower14 extent face)
  exact hcleared.trans
    (HaarCarrierEqv.mul hweight
      (HaarCarrierEqv.refl _ (globalPlaquetteVectorJet extent face)))

private theorem eval_constantPolynomial (rho : Nat → Q') (coefficient : Q') :
    evalRatPoly rho (polySmul coefficient polyOne) ≈ coefficient :=
  Q'.eqv_trans _ _ _ (evalRatPoly_smul rho coefficient polyOne)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (evalRatPoly_one rho))
      (Q'.mul_one_eqv coefficient))

private theorem eval_onePolynomial (rho : Nat → Q') :
    evalRatPoly rho (polySmul 1 polyOne) ≈ 1 :=
  eval_constantPolynomial rho 1

private theorem eval_coeffPolyPow (rho : Nat → Q') (polynomial : RatPoly) :
    ∀ exponent,
      evalRatPoly rho (coeffPolyPow polynomial exponent) ≈
        qpow (evalRatPoly rho polynomial) exponent
  | 0 => evalRatPoly_one rho
  | exponent + 1 =>
      Q'.eqv_trans _ _ _
        (evalRatPoly_mul rho (coeffPolyPow polynomial exponent) polynomial)
        (mc (eval_coeffPolyPow rho polynomial exponent) (Q'.eqv_refl _))

/-- Evaluation of one normalized north base is the existing rational
quaternion kernel base. -/
theorem northCayleyBasePolynomial_eval
    (rho : Nat → Q') (q : PolyQuaternion) (unit : UnitNorm)
    (hunit : QuaternionValue.Eqv
      (evalPolyQuaternion rho q) (unitValue unit)) :
    evalRatPoly rho (northCayleyBasePolynomial q) ≈ base unit := by
  have hscalar : evalRatPoly rho q.scalar ≈ unit.val.r := by
    simpa [evalPolyQuaternion, unitValue] using hunit.scalar
  have hdenominator :
      evalRatPoly rho (cayleyChartDenominatorPolynomial q) ≈
        (1 : Q') + unit.val.r :=
    Q'.eqv_trans _ _ _
      (evalRatPoly_add rho (polySmul 1 polyOne) q.scalar)
      (ac (eval_onePolynomial rho) hscalar)
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_smul rho half (cayleyChartDenominatorPolynomial q))
    (mc (Q'.eqv_refl half) hdenominator)

/-- On the actual oriented slab-link assignment, the polynomial base product
is exactly the existing four-unit kernel product. -/
theorem globalCayleyNorthBaseProduct_eval
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    evalRatPoly (environment qs)
      (globalCayleyNorthBaseProduct extent face) ≈
      product
        (orientedLinkValue extent qs (faceCayleyEntry0 face))
        (orientedLinkValue extent qs (faceCayleyEntry1 face))
        (orientedLinkValue extent qs (faceCayleyEntry2 face))
        (orientedLinkValue extent qs (faceCayleyEntry3 face)) := by
  have h0 := northCayleyBasePolynomial_eval (environment qs)
    (faceCayleyQuaternion0 extent face)
    (orientedLinkValue extent qs (faceCayleyEntry0 face))
    (oriented_link_eval extent qs (faceCayleyEntry0 face))
  have h1 := northCayleyBasePolynomial_eval (environment qs)
    (faceCayleyQuaternion1 extent face)
    (orientedLinkValue extent qs (faceCayleyEntry1 face))
    (oriented_link_eval extent qs (faceCayleyEntry1 face))
  have h2 := northCayleyBasePolynomial_eval (environment qs)
    (faceCayleyQuaternion2 extent face)
    (orientedLinkValue extent qs (faceCayleyEntry2 face))
    (oriented_link_eval extent qs (faceCayleyEntry2 face))
  have h3 := northCayleyBasePolynomial_eval (environment qs)
    (faceCayleyQuaternion3 extent face)
    (orientedLinkValue extent qs (faceCayleyEntry3 face))
    (oriented_link_eval extent qs (faceCayleyEntry3 face))
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_mul (environment qs) _ _)
    (mc
      (Q'.eqv_trans _ _ _ (evalRatPoly_mul (environment qs) _ _)
        (mc h0 h1))
      (Q'.eqv_trans _ _ _ (evalRatPoly_mul (environment qs) _ _)
        (mc h2 h3)))

/-- The normalized four-link north base product evaluates in the closed unit
interval, including the south-pole zero. -/
theorem globalCayleyNorthBaseProduct_eval_bounds
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    (0 : Q') ≤ evalRatPoly (environment qs)
        (globalCayleyNorthBaseProduct extent face) ∧
      evalRatPoly (environment qs)
        (globalCayleyNorthBaseProduct extent face) ≤ (1 : Q') := by
  have heval := globalCayleyNorthBaseProduct_eval extent qs face
  have hb := product_bounds
    (orientedLinkValue extent qs (faceCayleyEntry0 face))
    (orientedLinkValue extent qs (faceCayleyEntry1 face))
    (orientedLinkValue extent qs (faceCayleyEntry2 face))
    (orientedLinkValue extent qs (faceCayleyEntry3 face))
  exact ⟨
    Q'.le_trans' _ _ _ hb.1
      (Q'.le_of_eqv (Q'.eqv_symm heval)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heval) hb.2⟩

/-- The four-link base power evaluates to the four-kernel product raised to
the fourteenth power. -/
theorem globalCayleyNorthBasePower14_eval
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    evalRatPoly (environment qs)
      (globalCayleyNorthBasePower14 extent face) ≈
      qpow
        (product
          (orientedLinkValue extent qs (faceCayleyEntry0 face))
          (orientedLinkValue extent qs (faceCayleyEntry1 face))
          (orientedLinkValue extent qs (faceCayleyEntry2 face))
          (orientedLinkValue extent qs (faceCayleyEntry3 face))) 14 := by
  exact Q'.eqv_trans _ _ _
    (eval_coeffPolyPow (environment qs)
      (globalCayleyNorthBaseProduct extent face) 14)
    (qpow_eqv_congr
      (globalCayleyNorthBaseProduct_eval extent qs face) 14)

/-- Pointwise Bernoulli control of the exact north-weight loss.  This is the
literal error factor that a later centered ORIGINAL expectation must pay. -/
theorem globalCayleyNorthBasePower14_eval_deficit_le
    (extent : Nat) (qs : Nat → UnitNorm) (face : Z4Plaq) :
    (1 : Q') + -evalRatPoly (environment qs)
        (globalCayleyNorthBasePower14 extent face) ≤
      Q'.ofNat 14 *
        ((1 : Q') + -evalRatPoly (environment qs)
          (globalCayleyNorthBaseProduct extent face)) := by
  have hb := globalCayleyNorthBaseProduct_eval_bounds extent qs face
  have hp := eval_coeffPolyPow (environment qs)
    (globalCayleyNorthBaseProduct extent face) 14
  have heq : (1 : Q') + -evalRatPoly (environment qs)
      (globalCayleyNorthBasePower14 extent face) ≈
      (1 : Q') + -qpow
        (evalRatPoly (environment qs)
          (globalCayleyNorthBaseProduct extent face)) 14 :=
    Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _ hp)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (oneSub_qpow_le hb.1 hb.2 14)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.northCayleyBasePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthBaseProduct
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthScaledBasePower7
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthBasePower14
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthScaledBasePower14
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.cayleyChartDenominatorPolynomial_coeff_double_base
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthFactorProduct_coeff_scaledBasePower7
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthClearedWeight_coeff_scaledBasePower14
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyVectorJetClearedPolynomial_carrier_scaledBasePower14
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.northCayleyBasePolynomial_eval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthBaseProduct_eval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthBaseProduct_eval_bounds
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthBasePower14_eval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyNorthWeightNormalization.globalCayleyNorthBasePower14_eval_deficit_le
