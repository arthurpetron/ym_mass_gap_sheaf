/-
# Homogeneous signed-chart Cayley split and lossless reassembly

The public generic Cayley compiler is instantiated on each of the sixteen
signed four-link charts.  The actual cleared scalar deficit is identified on
the unchanged ORIGINAL Haar carrier with the compiled degree-two-through-six
deficit.  Each chart's cleared vector jet then splits into its compiled
quadratic term plus one explicit complete nonlinear residual.  Multiplication
by the certified subordinate quotient and finite summation reconstructs the
identity-scaled physical vector jet without a single-chart loss.

No residual estimate, ORIGINAL-to-FREE comparison, cutoff removal, continuum
Hamiltonian, or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetCayleyReassembly
import YMGap.Continuum.QuaternionHaarGammaFiniteSum

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetHomogeneous

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
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetCayleyReassembly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetReassembly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJet
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.QuaternionHaarGammaFiniteSum
  (finitePolySum_add)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

local infix:50 " ≈ " => Q'.eqv

def globalCayleySignedChartCompiledDenominatorPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  compiledCayleyDenominatorPolynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

def globalCayleySignedChartCompiledRawScalarPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  compiledCayleyRawScalarPolynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

def globalCayleySignedChartCompiledDeficitPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  compiledCayleyDeficitPolynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

def globalCayleySignedChartCompiledDegreeTwoPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  compiledCayleyDegreeTwoPolynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

def globalCayleySignedChartCompiledHigherPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  compiledCayleyHigherPolynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

def globalCayleySignedChartRawWordPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternion :=
  rawCayleyWordPolynomial
    (signedChartFaceQuaternion0 extent face chart)
    (signedChartFaceQuaternion1 extent face chart)
    (signedChartFaceQuaternion2 extent face chart)
    (signedChartFaceQuaternion3 extent face chart)

def globalCayleySignedChartClearedWordPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternion :=
  let q0 := signedChartFaceQuaternion0 extent face chart
  let q1 := signedChartFaceQuaternion1 extent face chart
  let q2 := signedChartFaceQuaternion2 extent face chart
  let q3 := signedChartFaceQuaternion3 extent face chart
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (PolyQuaternion.mul
        (clearedUnitFactor q0 (cayleyComplement0Polynomial q0 q1 q2 q3))
        (clearedUnitFactor q1 (cayleyComplement1Polynomial q0 q1 q2 q3)))
      (clearedUnitFactor q2 (cayleyComplement2Polynomial q0 q1 q2 q3)))
    (clearedUnitFactor q3 (cayleyComplement3Polynomial q0 q1 q2 q3))

private def scaleMulEnvironment
    (firstScale secondScale : RatPoly)
    (first second : PolyQuaternion) : Nat → RatPoly
  | 0 => firstScale
  | 1 => secondScale
  | 2 => first.scalar
  | 3 => first.iPart
  | 4 => first.jPart
  | 5 => first.kPart
  | 6 => second.scalar
  | 7 => second.iPart
  | 8 => second.jPart
  | 9 => second.kPart
  | _ => polyZero

private def scaleQuaternionExpr
    (scale : PolyExpr) (q : PolyQuaternionExpr) : PolyQuaternionExpr :=
  ⟨.mul scale q.scalar, .mul scale q.iPart,
    .mul scale q.jPart, .mul scale q.kPart⟩

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

private theorem polynomialScaleQuaternion_mul
    (firstScale secondScale : RatPoly) (first second : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul
        (polynomialScaleQuaternion firstScale first)
        (polynomialScaleQuaternion secondScale second))
      (polynomialScaleQuaternion (polyMul firstScale secondScale)
        (PolyQuaternion.mul first second)) := by
  let environment := scaleMulEnvironment firstScale secondScale first second
  let left := PolyQuaternionExpr.mul
    (scaleQuaternionExpr (.var 0) (PolyQuaternionExpr.coordinate 2))
    (scaleQuaternionExpr (.var 1) (PolyQuaternionExpr.coordinate 6))
  let right := scaleQuaternionExpr (.mul (.var 0) (.var 1))
    (PolyQuaternionExpr.mul
      (PolyQuaternionExpr.coordinate 2) (PolyQuaternionExpr.coordinate 6))
  have h := coeffEvalQuaternionExpr_eqv_of_normalize_eq environment left right
    (by decide) (by decide) (by decide) (by decide)
  simpa [environment, left, right, scaleMulEnvironment,
    polynomialScaleQuaternion, scaleQuaternionExpr,
    coeffEvalQuaternionExpr, PolyQuaternionExpr.mul,
    PolyQuaternionExpr.coordinate, coeffEvalExpr] using h

private def fourCayleyClearedWord
    (q0 q1 q2 q3 : PolyQuaternion)
    (complement0 complement1 complement2 complement3 : RatPoly) :
    PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (PolyQuaternion.mul
        (clearedUnitFactor q0 complement0)
        (clearedUnitFactor q1 complement1))
      (clearedUnitFactor q2 complement2))
    (clearedUnitFactor q3 complement3)

private def fourCayleyScaleProduct
    (q0 q1 q2 q3 : PolyQuaternion)
    (complement0 complement1 complement2 complement3 : RatPoly) : RatPoly :=
  polyMul
    (polyMul
      (polyMul
        (clearedCayleyFactorPolynomial q0 complement0)
        (clearedCayleyFactorPolynomial q1 complement1))
      (clearedCayleyFactorPolynomial q2 complement2))
    (clearedCayleyFactorPolynomial q3 complement3)

private def fourQuaternionWord
    (q0 q1 q2 q3 : PolyQuaternion) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul (PolyQuaternion.mul q0 q1) q2) q3

private theorem clearedCayleyWord_coeff_scale
    (q0 q1 q2 q3 : PolyQuaternion)
    (complement0 complement1 complement2 complement3 : RatPoly) :
    PolyQuaternionCoeffEqv
      (fourCayleyClearedWord q0 q1 q2 q3
        complement0 complement1 complement2 complement3)
      (polynomialScaleQuaternion
        (fourCayleyScaleProduct q0 q1 q2 q3
          complement0 complement1 complement2 complement3)
        (fourQuaternionWord q0 q1 q2 q3)) := by
  let scale0 := clearedCayleyFactorPolynomial q0 complement0
  let scale1 := clearedCayleyFactorPolynomial q1 complement1
  let scale2 := clearedCayleyFactorPolynomial q2 complement2
  let scale3 := clearedCayleyFactorPolynomial q3 complement3
  have h0 := clearedUnitFactor_coeff_scale q0 complement0
  have h1 := clearedUnitFactor_coeff_scale q1 complement1
  have h2 := clearedUnitFactor_coeff_scale q2 complement2
  have h3 := clearedUnitFactor_coeff_scale q3 complement3
  have hfactors := PolyQuaternionCoeffEqv.mul
    (PolyQuaternionCoeffEqv.mul
      (PolyQuaternionCoeffEqv.mul h0 h1) h2) h3
  have h01 := polynomialScaleQuaternion_mul scale0 scale1 q0 q1
  have h012 := polynomialScaleQuaternion_mul
    (polyMul scale0 scale1) scale2 (PolyQuaternion.mul q0 q1) q2
  have h0123 := polynomialScaleQuaternion_mul
    (polyMul (polyMul scale0 scale1) scale2) scale3
    (PolyQuaternion.mul (PolyQuaternion.mul q0 q1) q2) q3
  have hscaled012 := (PolyQuaternionCoeffEqv.mul h01
    (PolyQuaternionCoeffEqv.refl
      (polynomialScaleQuaternion scale2 q2))).trans h012
  have hscaled := (PolyQuaternionCoeffEqv.mul hscaled012
    (PolyQuaternionCoeffEqv.refl
      (polynomialScaleQuaternion scale3 q3))).trans h0123
  simpa [scale0, scale1, scale2, scale3,
    polynomialScaleQuaternion, fourCayleyClearedWord,
    fourCayleyScaleProduct, fourQuaternionWord] using hfactors.trans hscaled

private theorem globalCayleySignedChartClearedWord_coeff_scale
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternionCoeffEqv
      (globalCayleySignedChartClearedWordPolynomial extent face chart)
      (polynomialScaleQuaternion
        (globalCayleySignedChartScaleProduct extent face chart)
        (globalCayleySignedChartQuaternionWord extent face chart)) := by
  let q0 := signedChartFaceQuaternion0 extent face chart
  let q1 := signedChartFaceQuaternion1 extent face chart
  let q2 := signedChartFaceQuaternion2 extent face chart
  let q3 := signedChartFaceQuaternion3 extent face chart
  let c0 := signedChartComplement0 extent face chart
  let c1 := signedChartComplement1 extent face chart
  let c2 := signedChartComplement2 extent face chart
  let c3 := signedChartComplement3 extent face chart
  simpa [q0, q1, q2, q3, c0, c1, c2, c3,
    globalCayleySignedChartClearedWordPolynomial,
    globalCayleySignedChartScaleProduct,
    globalCayleySignedChartQuaternionWord,
    signedChartComplement0, signedChartComplement1,
    signedChartComplement2, signedChartComplement3,
    clearedCayleyScaleProduct] using
      (clearedCayleyWord_coeff_scale q0 q1 q2 q3 c0 c1 c2 c3)

private theorem globalCayleySignedChartRawWord_carrier_clear
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    PolyQuaternionHaarCarrierEqv
      (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartRawWordPolynomial extent face chart)
      (globalCayleySignedChartClearedWordPolynomial extent face chart) := by
  let q0 := signedChartFaceQuaternion0 extent face chart
  let q1 := signedChartFaceQuaternion1 extent face chart
  let q2 := signedChartFaceQuaternion2 extent face chart
  let q3 := signedChartFaceQuaternion3 extent face chart
  have h0 : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm q0) polyOne := by
    exact haarNorm_signedChartQuaternion chart.south0
      (haarNorm_orientedCorrectedSlabLinkPolynomial extent
        (faceCayleyEntry0 face))
  have h1 : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm q1) polyOne := by
    exact haarNorm_signedChartQuaternion chart.south1
      (haarNorm_orientedCorrectedSlabLinkPolynomial extent
        (faceCayleyEntry1 face))
  have h2 : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm q2) polyOne := by
    exact haarNorm_signedChartQuaternion chart.south2
      (haarNorm_orientedCorrectedSlabLinkPolynomial extent
        (faceCayleyEntry2 face))
  have h3 : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm q3) polyOne := by
    exact haarNorm_signedChartQuaternion chart.south3
      (haarNorm_orientedCorrectedSlabLinkPolynomial extent
        (faceCayleyEntry3 face))
  exact rawCayleyWord_carrier_clear
    q0 q1 q2 q3
    (signedChartComplement0 extent face chart)
    (signedChartComplement1 extent face chart)
    (signedChartComplement2 extent face chart)
    (signedChartComplement3 extent face chart)
    h0 h1 h2 h3

private theorem globalCayleySignedChartRawScalar_carrier_scale
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartRawWordPolynomial extent face chart).scalar
      (polyMul (globalCayleySignedChartScaleProduct extent face chart)
        (globalCayleySignedChartScalar extent face chart)) := by
  have hraw := globalCayleySignedChartRawWord_carrier_clear
    extent face chart
  have hscale := globalCayleySignedChartClearedWord_coeff_scale
    extent face chart
  have hscaleScalar : RatPolyCoeffEqv
      (globalCayleySignedChartClearedWordPolynomial extent face chart).scalar
      (polyMul (globalCayleySignedChartScaleProduct extent face chart)
        (globalCayleySignedChartScalar extent face chart)) := by
    simpa only [polynomialScaleQuaternion,
      globalCayleySignedChartScalar] using hscale.scalar
  exact hraw.scalar.trans (RatPolyCoeffEqv.haarCarrier hscaleScalar)

private theorem globalCayleySignedChartCompiledDenominator_carrier_scale
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartCompiledDenominatorPolynomial extent face chart)
      (globalCayleySignedChartScaleProduct extent face chart) := by
  let q0 := signedChartFaceQuaternion0 extent face chart
  let q1 := signedChartFaceQuaternion1 extent face chart
  let q2 := signedChartFaceQuaternion2 extent face chart
  let q3 := signedChartFaceQuaternion3 extent face chart
  exact RatPolyCoeffEqv.haarCarrier
    (by
      simpa [q0, q1, q2, q3,
        globalCayleySignedChartCompiledDenominatorPolynomial,
        globalCayleySignedChartScaleProduct] using
        (clearedCayleyScaleProduct_coeff_compiled q0 q1 q2 q3).symm)

private theorem globalCayleySignedChartCompiledRawScalar_carrier_scale
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartCompiledRawScalarPolynomial extent face chart)
      (polyMul (globalCayleySignedChartScaleProduct extent face chart)
        (globalCayleySignedChartScalar extent face chart)) := by
  let q0 := signedChartFaceQuaternion0 extent face chart
  let q1 := signedChartFaceQuaternion1 extent face chart
  let q2 := signedChartFaceQuaternion2 extent face chart
  let q3 := signedChartFaceQuaternion3 extent face chart
  have hcompiled :=
    rawCayleyWordPolynomial_scalar_coeff_compiled q0 q1 q2 q3
  have hraw := globalCayleySignedChartRawScalar_carrier_scale
    extent face chart
  exact (RatPolyCoeffEqv.haarCarrier (by
    simpa [q0, q1, q2, q3,
      globalCayleySignedChartRawWordPolynomial,
      globalCayleySignedChartCompiledRawScalarPolynomial] using
        hcompiled.symm)).trans hraw

private def globalCayleySignedChartNormalizedDeficitPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  let two := polySmul (Q'.ofInt 2) polyOne
  let scale := globalCayleySignedChartScaleProduct extent face chart
  let scalar := globalCayleySignedChartScalar extent face chart
  polyMul scale
    (polyAdd two (polyNeg (polyMul two scalar)))

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

private theorem globalCayleySignedChartDeficit_coeff_normalized
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    RatPolyCoeffEqv
      (globalCayleySignedChartDeficitPolynomial extent face chart)
      (globalCayleySignedChartNormalizedDeficitPolynomial
        extent face chart) := by
  let scale := globalCayleySignedChartScaleProduct extent face chart
  let scalar := globalCayleySignedChartScalar extent face chart
  let htwo := polyConst_coeff_smul (Q'.ofInt 2)
  unfold globalCayleySignedChartDeficitPolynomial
    globalCayleySignedChartNormalizedDeficitPolynomial
  exact RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl scale)
    (htwo.add (RatPolyCoeffEqv.neg
      (RatPolyCoeffEqv.mul htwo (RatPolyCoeffEqv.refl scalar))))

/-- The literal signed scalar deficit is the generic compiled homogeneous
Cayley deficit on the unchanged ORIGINAL Haar carrier. -/
theorem globalCayleySignedChartDeficit_carrier_compiled
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartDeficitPolynomial extent face chart)
      (globalCayleySignedChartCompiledDeficitPolynomial
        extent face chart) := by
  let q0 := signedChartFaceQuaternion0 extent face chart
  let q1 := signedChartFaceQuaternion1 extent face chart
  let q2 := signedChartFaceQuaternion2 extent face chart
  let q3 := signedChartFaceQuaternion3 extent face chart
  let two := polySmul (Q'.ofInt 2) polyOne
  let scale := globalCayleySignedChartScaleProduct extent face chart
  let scalar := globalCayleySignedChartScalar extent face chart
  let denominator := globalCayleySignedChartCompiledDenominatorPolynomial
    extent face chart
  let rawScalar := globalCayleySignedChartCompiledRawScalarPolynomial
    extent face chart
  let compiledDeficit := globalCayleySignedChartCompiledDeficitPolynomial
    extent face chart
  let normalizedDeficit :=
    globalCayleySignedChartNormalizedDeficitPolynomial extent face chart
  have hraw := compiledCayleyDeficitPolynomial_coeff_raw q0 q1 q2 q3
  change RatPolyCoeffEqv compiledDeficit
    (polyAdd (polyMul two denominator)
      (polyNeg (polyMul two rawScalar))) at hraw
  have hden := globalCayleySignedChartCompiledDenominator_carrier_scale
    extent face chart
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    denominator scale at hden
  have hscalar := globalCayleySignedChartCompiledRawScalar_carrier_scale
    extent face chart
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    rawScalar (polyMul scale scalar) at hscalar
  have hreplace : HaarCarrierEqv
      (boundaryCompleteSlabLinks extent).length
      (polyAdd (polyMul two denominator)
        (polyNeg (polyMul two rawScalar)))
      (polyAdd (polyMul two scale)
        (polyNeg (polyMul two (polyMul scale scalar)))) :=
    HaarCarrierEqv.add
      (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ two) hden)
      (HaarCarrierEqv.neg
        (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ two) hscalar))
  have hshape : RatPolyCoeffEqv
      (polyAdd (polyMul two scale)
        (polyNeg (polyMul two (polyMul scale scalar))))
      normalizedDeficit := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 0) (.mul (.var 1) (.var 2)))))
      (.mul (.var 1)
        (.add (.var 0) (.neg (.mul (.var 0) (.var 2)))))
      (by decide)
      (fun | 0 => two | 1 => scale | _ => scalar)
  have hcompiled : HaarCarrierEqv
      (boundaryCompleteSlabLinks extent).length
      compiledDeficit normalizedDeficit :=
    (RatPolyCoeffEqv.haarCarrier hraw).trans
      (hreplace.trans (RatPolyCoeffEqv.haarCarrier hshape))
  exact (RatPolyCoeffEqv.haarCarrier
    (globalCayleySignedChartDeficit_coeff_normalized
      extent face chart)).trans hcompiled.symm

theorem globalCayleySignedChartCompiledDeficit_coeff_quadratic_higher
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) :
    RatPolyCoeffEqv
      (globalCayleySignedChartCompiledDeficitPolynomial extent face chart)
      (polyAdd
        (globalCayleySignedChartCompiledDegreeTwoPolynomial
          extent face chart)
        (globalCayleySignedChartCompiledHigherPolynomial
          extent face chart)) := by
  let q0 := signedChartFaceQuaternion0 extent face chart
  let q1 := signedChartFaceQuaternion1 extent face chart
  let q2 := signedChartFaceQuaternion2 extent face chart
  let q3 := signedChartFaceQuaternion3 extent face chart
  have hdegrees := compiledCayleyDeficitPolynomial_coeff_degrees
    q0 q1 q2 q3
  let p2 := compiledCayleyDegreeTwoPolynomial q0 q1 q2 q3
  let p3 := compiledCayleyDegreeThreePolynomial q0 q1 q2 q3
  let p4 := compiledCayleyDegreeFourPolynomial q0 q1 q2 q3
  let p5 := compiledCayleyDegreeFivePolynomial q0 q1 q2 q3
  let p6 := compiledCayleyDegreeSixPolynomial q0 q1 q2 q3
  have hregroup : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyAdd (polyAdd p2 p3) p4) p5) p6)
      (polyAdd p2
        (polyAdd (polyAdd p3 p4) (polyAdd p5 p6))) := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (((.var 0 + .var 1) + .var 2) + .var 3 + .var 4)
      (.var 0 + ((.var 1 + .var 2) + (.var 3 + .var 4)))
      (by decide)
      (fun | 0 => p2 | 1 => p3 | 2 => p4 | 3 => p5 | _ => p6)
  simpa [q0, q1, q2, q3, p2, p3, p4, p5, p6,
    globalCayleySignedChartCompiledDeficitPolynomial,
    globalCayleySignedChartCompiledDegreeTwoPolynomial,
    globalCayleySignedChartCompiledHigherPolynomial,
    compiledCayleyHigherPolynomial] using hdegrees.trans hregroup

def globalCayleySignedChartQuadraticPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (polyMul (polyConst 4)
      (globalCayleySignedChartScaleProduct extent face chart))
    (globalCayleySignedChartCompiledDegreeTwoPolynomial extent face chart)

def globalCayleySignedChartHomogeneousRemainderPolynomial
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  let scale := globalCayleySignedChartScaleProduct extent face chart
  let deficit := globalCayleySignedChartCompiledDeficitPolynomial
    extent face chart
  polyAdd
    (polyMul (polyMul (polyConst 4) scale)
      (globalCayleySignedChartCompiledHigherPolynomial extent face chart))
    (polyNeg (polyMul deficit deficit))

/-- The actual signed-chart cleared vector jet is its compiled homogeneous
quadratic part plus one complete degree-three-through-twelve residual. -/
theorem globalCayleySignedChartVectorJetCleared_carrier_homogeneous
    {extent : Nat} {face : Z4Plaq} (chart : FourCayleyChart)
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartVectorJetClearedPolynomial extent face chart)
      (polyAdd
        (globalCayleySignedChartQuadraticPolynomial extent face chart)
        (globalCayleySignedChartHomogeneousRemainderPolynomial
          extent face chart)) := by
  let scale := globalCayleySignedChartScaleProduct extent face chart
  let actualDeficit := globalCayleySignedChartDeficitPolynomial
    extent face chart
  let deficit := globalCayleySignedChartCompiledDeficitPolynomial
    extent face chart
  let quadratic := globalCayleySignedChartCompiledDegreeTwoPolynomial
    extent face chart
  let higher := globalCayleySignedChartCompiledHigherPolynomial
    extent face chart
  let fourScale := polyMul (polyConst 4) scale
  have hbase := globalCayleySignedChartVectorJetCleared_carrier_cayley
    chart hface
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleySignedChartVectorJetClearedPolynomial extent face chart)
    (polyAdd (polyMul fourScale actualDeficit)
      (polyNeg (polyMul actualDeficit actualDeficit))) at hbase
  have hdeficit := globalCayleySignedChartDeficit_carrier_compiled
    extent face chart
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    actualDeficit deficit at hdeficit
  have hreplace : HaarCarrierEqv
      (boundaryCompleteSlabLinks extent).length
      (polyAdd (polyMul fourScale actualDeficit)
        (polyNeg (polyMul actualDeficit actualDeficit)))
      (polyAdd (polyMul fourScale deficit)
        (polyNeg (polyMul deficit deficit))) :=
    HaarCarrierEqv.add
      (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ fourScale) hdeficit)
      (HaarCarrierEqv.neg (HaarCarrierEqv.mul hdeficit hdeficit))
  have hsplit :=
    globalCayleySignedChartCompiledDeficit_coeff_quadratic_higher
      extent face chart
  change RatPolyCoeffEqv deficit (polyAdd quadratic higher) at hsplit
  have hsplitReplace : RatPolyCoeffEqv
      (polyAdd (polyMul fourScale deficit)
        (polyNeg (polyMul deficit deficit)))
      (polyAdd (polyMul fourScale (polyAdd quadratic higher))
        (polyNeg (polyMul deficit deficit))) :=
    (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.refl fourScale) hsplit).add
      (RatPolyCoeffEqv.refl _)
  have hregroup : RatPolyCoeffEqv
      (polyAdd (polyMul fourScale (polyAdd quadratic higher))
        (polyNeg (polyMul deficit deficit)))
      (polyAdd (polyMul fourScale quadratic)
        (polyAdd (polyMul fourScale higher)
          (polyNeg (polyMul deficit deficit)))) := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.var 1) (.var 2)))
        (.neg (.mul (.var 3) (.var 3))))
      (.add (.mul (.var 0) (.var 1))
        (.add (.mul (.var 0) (.var 2))
          (.neg (.mul (.var 3) (.var 3)))))
      (by decide)
      (fun | 0 => fourScale | 1 => quadratic | 2 => higher | _ => deficit)
  change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
    (globalCayleySignedChartVectorJetClearedPolynomial extent face chart)
    (polyAdd (polyMul fourScale quadratic)
      (polyAdd (polyMul fourScale higher)
        (polyNeg (polyMul deficit deficit))))
  exact hbase.trans (hreplace.trans
    (RatPolyCoeffEqv.haarCarrier (hsplitReplace.trans hregroup)))

def globalCayleySignedChartQuadraticReassemblyTerm
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (globalCayleySubordinateChartQuotientPolynomial extent face chart)
    (globalCayleySignedChartQuadraticPolynomial extent face chart)

def globalCayleySignedChartRemainderReassemblyTerm
    (extent : Nat) (face : Z4Plaq) (chart : FourCayleyChart) : RatPoly :=
  polyMul
    (globalCayleySubordinateChartQuotientPolynomial extent face chart)
    (globalCayleySignedChartHomogeneousRemainderPolynomial
      extent face chart)

def globalCayleySignedChartQuadraticReassemblyPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  finitePolySum
    (globalCayleySignedChartQuadraticReassemblyTerm extent face)
    fourCayleyChartTable

def globalCayleySignedChartRemainderReassemblyPolynomial
    (extent : Nat) (face : Z4Plaq) : RatPoly :=
  finitePolySum
    (globalCayleySignedChartRemainderReassemblyTerm extent face)
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

/-- The identity-scaled physical vector jet is the complete quotient-weighted
signed-chart quadratic sum plus the complete quotient-weighted nonlinear
residual, with no chart loss. -/
theorem globalCayleySignedChartHomogeneousReassembly_carrier_identityScaled
    {extent : Nat} {face : Z4Plaq}
    (hface : face ∈ boundaryCompleteSlabPlaquettes extent) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyMul (polySmul (Q'.ofInt (2 ^ 66)) polyOne)
        (globalPlaquetteVectorJet extent face))
      (polyAdd
        (globalCayleySignedChartQuadraticReassemblyPolynomial extent face)
        (globalCayleySignedChartRemainderReassemblyPolynomial
          extent face)) := by
  let actual := globalCayleySignedChartReassemblyTerm extent face
  let quadratic := globalCayleySignedChartQuadraticReassemblyTerm extent face
  let remainder := globalCayleySignedChartRemainderReassemblyTerm extent face
  have hpoint : ∀ chart, chart ∈ fourCayleyChartTable →
      HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
        (actual chart) (polyAdd (quadratic chart) (remainder chart)) := by
    intro chart _
    let quotient := globalCayleySubordinateChartQuotientPolynomial
      extent face chart
    have hsplit :=
      globalCayleySignedChartVectorJetCleared_carrier_homogeneous
        chart hface
    have hscaled := HaarCarrierEqv.mul
      (HaarCarrierEqv.refl _ quotient) hsplit
    exact hscaled.trans (RatPolyCoeffEqv.haarCarrier
      (RatPolyCoeffEqv.mul_add_right quotient
        (globalCayleySignedChartQuadraticPolynomial extent face chart)
        (globalCayleySignedChartHomogeneousRemainderPolynomial
          extent face chart)))
  have hsum := finiteSum_carrier
    (boundaryCompleteSlabLinks extent).length actual
    (fun chart => polyAdd (quadratic chart) (remainder chart))
    fourCayleyChartTable hpoint
  have hseparate := finitePolySum_add quadratic remainder fourCayleyChartTable
  have hsplit : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleySignedChartReassemblyPolynomial extent face)
      (polyAdd
        (globalCayleySignedChartQuadraticReassemblyPolynomial extent face)
        (globalCayleySignedChartRemainderReassemblyPolynomial
          extent face)) := by
    change HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (finitePolySum actual fourCayleyChartTable)
      (polyAdd
        (finitePolySum quadratic fourCayleyChartTable)
        (finitePolySum remainder fourCayleyChartTable))
    exact hsum.trans (RatPolyCoeffEqv.haarCarrier hseparate)
  exact (globalCayleySignedChartReassembly_carrier_identityScaled
    extent face).symm.trans hsplit

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetHomogeneous

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetHomogeneous.globalCayleySignedChartDeficit_carrier_compiled
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetHomogeneous.globalCayleySignedChartCompiledDeficit_coeff_quadratic_higher
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetHomogeneous.globalCayleySignedChartVectorJetCleared_carrier_homogeneous
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetHomogeneous.globalCayleySignedChartHomogeneousReassembly_carrier_identityScaled
