/-
# Four-factor global Cayley clearing on the ORIGINAL slab Haar carrier

The one-factor carrier identity is composed over the four literally oriented
plaquette links.  The identity fallback is handled explicitly, so this module
does not assume that the supplied face belongs to the physical slab list.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
import YMGap.Continuum.BF4ExactSlabPolynomialExpectation

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyRatPoly
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress

def polynomialScaleQuaternion
    (scale : RatPoly) (q : PolyQuaternion) : PolyQuaternion :=
  ⟨polyMul scale q.scalar, polyMul scale q.iPart,
    polyMul scale q.jPart, polyMul scale q.kPart⟩

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
  ⟨coeffEvalExpr_eqv_of_normalize_eq left.scalar right.scalar hscalar environment,
    coeffEvalExpr_eqv_of_normalize_eq left.iPart right.iPart hiPart environment,
    coeffEvalExpr_eqv_of_normalize_eq left.jPart right.jPart hjPart environment,
    coeffEvalExpr_eqv_of_normalize_eq left.kPart right.kPart hkPart environment⟩

/-- Scalar polynomial factors pull through Hamilton multiplication
coefficientwise. -/
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

private theorem polynomialScaleQuaternion_congr
    {firstScale secondScale : RatPoly} {first second : PolyQuaternion}
    (hscale : RatPolyCoeffEqv firstScale secondScale)
    (hquaternion : PolyQuaternionCoeffEqv first second) :
    PolyQuaternionCoeffEqv
      (polynomialScaleQuaternion firstScale first)
      (polynomialScaleQuaternion secondScale second) :=
  ⟨hscale.mul hquaternion.scalar,
    hscale.mul hquaternion.iPart,
    hscale.mul hquaternion.jPart,
    hscale.mul hquaternion.kPart⟩

/-- Haar-unit norm for every oriented corrected-slab link polynomial.  Outside
the slab link list the polynomial is the identity fallback, which is unit too. -/
theorem haarNorm_orientedCorrectedSlabLinkPolynomial
    (extent : Nat) (entry : OrientedBF4Link) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyQuaternionNorm
        (orientedCorrectedSlabLinkPolynomial extent entry)) polyOne := by
  by_cases hlink : entry.link ∈ boundaryCompleteSlabLinks extent
  · exact haarNorm_orientedSlabLink entry hlink
  · unfold orientedCorrectedSlabLinkPolynomial
    split
    · rw [correctedSlabLinkPolynomial_of_not_mem hlink]
      exact HaarCarrierEqv.trans
        (RatPolyCoeffEqv.haarCarrier
          (polyQuaternionNorm_conj PolyQuaternion.one))
        (RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one)
    · rw [correctedSlabLinkPolynomial_of_not_mem hlink]
      exact RatPolyCoeffEqv.haarCarrier polyQuaternionNorm_one

/-- Four one-factor clearings compose without any disjoint-link premise. -/
theorem rawCayleyWord_carrier_clear
    {blocks : Nat} (q0 q1 q2 q3 : PolyQuaternion)
    (complement0 complement1 complement2 complement3 : RatPoly)
    (h0 : HaarCarrierEqv blocks (polyQuaternionNorm q0) polyOne)
    (h1 : HaarCarrierEqv blocks (polyQuaternionNorm q1) polyOne)
    (h2 : HaarCarrierEqv blocks (polyQuaternionNorm q2) polyOne)
    (h3 : HaarCarrierEqv blocks (polyQuaternionNorm q3) polyOne) :
    PolyQuaternionHaarCarrierEqv blocks
      (PolyQuaternion.mul
        (PolyQuaternion.mul
          (PolyQuaternion.mul
            (rawCayleyFactor q0 complement0)
            (rawCayleyFactor q1 complement1))
          (rawCayleyFactor q2 complement2))
        (rawCayleyFactor q3 complement3))
      (PolyQuaternion.mul
        (PolyQuaternion.mul
          (PolyQuaternion.mul
            (clearedUnitFactor q0 complement0)
            (clearedUnitFactor q1 complement1))
          (clearedUnitFactor q2 complement2))
        (clearedUnitFactor q3 complement3)) :=
  PolyQuaternionHaarCarrierEqv.mul
    (PolyQuaternionHaarCarrierEqv.mul
      (PolyQuaternionHaarCarrierEqv.mul
        (rawCayleyFactor_carrier_clear q0 complement0 h0)
        (rawCayleyFactor_carrier_clear q1 complement1 h1))
      (rawCayleyFactor_carrier_clear q2 complement2 h2))
    (rawCayleyFactor_carrier_clear q3 complement3 h3)

/-- The four literal oriented entries of a plaquette boundary. -/
def faceCayleyEntry0 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(face.1, (dirsOf face.2).1), false⟩

def faceCayleyEntry1 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(addE face.1 (dirsOf face.2).1, (dirsOf face.2).2), false⟩

def faceCayleyEntry2 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(addE face.1 (dirsOf face.2).2, (dirsOf face.2).1), true⟩

def faceCayleyEntry3 (face : Z4Plaq) : OrientedBF4Link :=
  ⟨(face.1, (dirsOf face.2).2), true⟩

def faceCayleyQuaternion0 (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  orientedCorrectedSlabLinkPolynomial extent (faceCayleyEntry0 face)

def faceCayleyQuaternion1 (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  orientedCorrectedSlabLinkPolynomial extent (faceCayleyEntry1 face)

def faceCayleyQuaternion2 (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  orientedCorrectedSlabLinkPolynomial extent (faceCayleyEntry2 face)

def faceCayleyQuaternion3 (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  orientedCorrectedSlabLinkPolynomial extent (faceCayleyEntry3 face)

def chartDenominatorPolynomial (q : PolyQuaternion) : RatPoly :=
  cayleyChartDenominatorPolynomial q

def faceCayleyComplement0 (extent : Nat) (face : Z4Plaq) : RatPoly :=
  cayleyComplement0Polynomial
    (faceCayleyQuaternion0 extent face)
    (faceCayleyQuaternion1 extent face)
    (faceCayleyQuaternion2 extent face)
    (faceCayleyQuaternion3 extent face)

def faceCayleyComplement1 (extent : Nat) (face : Z4Plaq) : RatPoly :=
  cayleyComplement1Polynomial
    (faceCayleyQuaternion0 extent face)
    (faceCayleyQuaternion1 extent face)
    (faceCayleyQuaternion2 extent face)
    (faceCayleyQuaternion3 extent face)

def faceCayleyComplement2 (extent : Nat) (face : Z4Plaq) : RatPoly :=
  cayleyComplement2Polynomial
    (faceCayleyQuaternion0 extent face)
    (faceCayleyQuaternion1 extent face)
    (faceCayleyQuaternion2 extent face)
    (faceCayleyQuaternion3 extent face)

def faceCayleyComplement3 (extent : Nat) (face : Z4Plaq) : RatPoly :=
  cayleyComplement3Polynomial
    (faceCayleyQuaternion0 extent face)
    (faceCayleyQuaternion1 extent face)
    (faceCayleyQuaternion2 extent face)
    (faceCayleyQuaternion3 extent face)

/-- Raw common-denominator word on the four ORIGINAL oriented link
polynomials. -/
def faceRawCayleyWord (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  rawCayleyWordPolynomial
    (faceCayleyQuaternion0 extent face)
    (faceCayleyQuaternion1 extent face)
    (faceCayleyQuaternion2 extent face)
    (faceCayleyQuaternion3 extent face)

/-- Product of the four cleared scalar multiples of the ORIGINAL oriented
link polynomials. -/
def faceClearedCayleyWord (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (PolyQuaternion.mul
        (clearedUnitFactor (faceCayleyQuaternion0 extent face)
          (faceCayleyComplement0 extent face))
        (clearedUnitFactor (faceCayleyQuaternion1 extent face)
          (faceCayleyComplement1 extent face)))
      (clearedUnitFactor (faceCayleyQuaternion2 extent face)
        (faceCayleyComplement2 extent face)))
    (clearedUnitFactor (faceCayleyQuaternion3 extent face)
      (faceCayleyComplement3 extent face))

def faceCayleyScale0 (extent : Nat) (face : Z4Plaq) : RatPoly :=
  clearedCayleyFactorPolynomial (faceCayleyQuaternion0 extent face)
    (faceCayleyComplement0 extent face)

def faceCayleyScale1 (extent : Nat) (face : Z4Plaq) : RatPoly :=
  clearedCayleyFactorPolynomial (faceCayleyQuaternion1 extent face)
    (faceCayleyComplement1 extent face)

def faceCayleyScale2 (extent : Nat) (face : Z4Plaq) : RatPoly :=
  clearedCayleyFactorPolynomial (faceCayleyQuaternion2 extent face)
    (faceCayleyComplement2 extent face)

def faceCayleyScale3 (extent : Nat) (face : Z4Plaq) : RatPoly :=
  clearedCayleyFactorPolynomial (faceCayleyQuaternion3 extent face)
    (faceCayleyComplement3 extent face)

def faceCayleyScaleProduct (extent : Nat) (face : Z4Plaq) : RatPoly :=
  clearedCayleyScaleProduct
    (faceCayleyQuaternion0 extent face)
    (faceCayleyQuaternion1 extent face)
    (faceCayleyQuaternion2 extent face)
    (faceCayleyQuaternion3 extent face)

def faceCayleyQuaternionWord (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  PolyQuaternion.mul
    (PolyQuaternion.mul
      (PolyQuaternion.mul
        (faceCayleyQuaternion0 extent face)
        (faceCayleyQuaternion1 extent face))
      (faceCayleyQuaternion2 extent face))
    (faceCayleyQuaternion3 extent face)

/-- The cleared four-factor word is coefficientwise one scalar polynomial
times the ordered product of the four literal oriented link polynomials. -/
theorem faceClearedCayleyWord_coeff_scale
    (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv
      (faceClearedCayleyWord extent face)
      (polynomialScaleQuaternion (faceCayleyScaleProduct extent face)
        (faceCayleyQuaternionWord extent face)) := by
  let q0 := faceCayleyQuaternion0 extent face
  let q1 := faceCayleyQuaternion1 extent face
  let q2 := faceCayleyQuaternion2 extent face
  let q3 := faceCayleyQuaternion3 extent face
  let complement0 := faceCayleyComplement0 extent face
  let complement1 := faceCayleyComplement1 extent face
  let complement2 := faceCayleyComplement2 extent face
  let complement3 := faceCayleyComplement3 extent face
  let scale0 := faceCayleyScale0 extent face
  let scale1 := faceCayleyScale1 extent face
  let scale2 := faceCayleyScale2 extent face
  let scale3 := faceCayleyScale3 extent face
  have h0 := clearedUnitFactor_coeff_scale q0 complement0
  have h1 := clearedUnitFactor_coeff_scale q1 complement1
  have h2 := clearedUnitFactor_coeff_scale q2 complement2
  have h3 := clearedUnitFactor_coeff_scale q3 complement3
  have hfactors : PolyQuaternionCoeffEqv
      (PolyQuaternion.mul
        (PolyQuaternion.mul
          (PolyQuaternion.mul
            (clearedUnitFactor q0 complement0)
            (clearedUnitFactor q1 complement1))
          (clearedUnitFactor q2 complement2))
        (clearedUnitFactor q3 complement3))
      (PolyQuaternion.mul
        (PolyQuaternion.mul
          (PolyQuaternion.mul
            (polynomialScaleQuaternion scale0 q0)
            (polynomialScaleQuaternion scale1 q1))
          (polynomialScaleQuaternion scale2 q2))
        (polynomialScaleQuaternion scale3 q3)) :=
    PolyQuaternionCoeffEqv.mul
      (PolyQuaternionCoeffEqv.mul
        (PolyQuaternionCoeffEqv.mul h0 h1) h2) h3
  have h01 := polynomialScaleQuaternion_mul scale0 scale1 q0 q1
  have h012 := polynomialScaleQuaternion_mul
    (polyMul scale0 scale1) scale2 (PolyQuaternion.mul q0 q1) q2
  have h0123 := polynomialScaleQuaternion_mul
    (polyMul (polyMul scale0 scale1) scale2) scale3
    (PolyQuaternion.mul (PolyQuaternion.mul q0 q1) q2) q3
  have hscaled012 := PolyQuaternionCoeffEqv.trans
    (PolyQuaternionCoeffEqv.mul h01
      (PolyQuaternionCoeffEqv.refl (polynomialScaleQuaternion scale2 q2)))
    h012
  have hscaled := PolyQuaternionCoeffEqv.trans
    (PolyQuaternionCoeffEqv.mul hscaled012
      (PolyQuaternionCoeffEqv.refl (polynomialScaleQuaternion scale3 q3)))
    h0123
  simpa [q0, q1, q2, q3, complement0, complement1, complement2, complement3,
    scale0, scale1, scale2, scale3, faceClearedCayleyWord,
    faceCayleyScaleProduct, faceCayleyQuaternionWord,
    faceCayleyScale0, faceCayleyScale1, faceCayleyScale2, faceCayleyScale3,
    polynomialScaleQuaternion] using hfactors.trans hscaled

/-- The four-factor oriented word is the literal corrected-slab plaquette
polynomial, up to the coefficient equality contributed by the initial
identity quaternion. -/
theorem correctedSlabPlaquettePolynomial_coeff_faceCayleyQuaternionWord
    (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv
      (correctedSlabPlaquettePolynomial extent face)
      (faceCayleyQuaternionWord extent face) := by
  have h := PolyQuaternionCoeffEqv.mul
    (PolyQuaternionCoeffEqv.mul
      (PolyQuaternionCoeffEqv.mul
        (PolyQuaternionCoeffEqv.one_mul
          (faceCayleyQuaternion0 extent face))
        (PolyQuaternionCoeffEqv.refl
          (faceCayleyQuaternion1 extent face)))
      (PolyQuaternionCoeffEqv.refl
        (faceCayleyQuaternion2 extent face)))
    (PolyQuaternionCoeffEqv.refl
      (faceCayleyQuaternion3 extent face))
  simpa [correctedSlabPlaquettePolynomial, orientedPlaquetteBoundary,
    faceCayleyQuaternionWord, faceCayleyQuaternion0, faceCayleyQuaternion1,
    faceCayleyQuaternion2, faceCayleyQuaternion3, faceCayleyEntry0,
    faceCayleyEntry1, faceCayleyEntry2, faceCayleyEntry3] using h

/-- The cleared word is coefficientwise its scalar factor product times the
SAME ORIGINAL corrected-slab plaquette polynomial. -/
theorem faceClearedCayleyWord_coeff_originalPlaquette
    (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv
      (faceClearedCayleyWord extent face)
      (polynomialScaleQuaternion (faceCayleyScaleProduct extent face)
        (correctedSlabPlaquettePolynomial extent face)) :=
  (faceClearedCayleyWord_coeff_scale extent face).trans
    (polynomialScaleQuaternion_congr
      (RatPolyCoeffEqv.refl (faceCayleyScaleProduct extent face))
      (correctedSlabPlaquettePolynomial_coeff_faceCayleyQuaternionWord
        extent face).symm)

/-- The scalar multiplying the cleared word is the literal global denominator
probe already used by the two ORIGINAL Cayley polynomials. -/
theorem faceCayleyScaleProduct_coeff_globalDenominator
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (faceCayleyScaleProduct extent face)
      (globalCayleyDenominatorPolynomial extent face) := by
  have hcompiled := clearedCayleyScaleProduct_coeff_compiled
    (faceCayleyQuaternion0 extent face)
    (faceCayleyQuaternion1 extent face)
    (faceCayleyQuaternion2 extent face)
    (faceCayleyQuaternion3 extent face)
  have hface := globalCayleyDenominatorPolynomial_coeff_compiled extent face
  simpa [faceCayleyScaleProduct, faceCayleyQuaternion0,
    faceCayleyQuaternion1, faceCayleyQuaternion2, faceCayleyQuaternion3,
    faceCayleyEntry0, faceCayleyEntry1, faceCayleyEntry2,
    faceCayleyEntry3] using hcompiled.trans hface.symm

/-- The full raw Cayley word clears on the ORIGINAL slab Haar carrier while
retaining every arbitrary polynomial insertion. -/
theorem faceRawCayleyWord_carrier_clear (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionHaarCarrierEqv
      (boundaryCompleteSlabLinks extent).length
      (faceRawCayleyWord extent face)
      (faceClearedCayleyWord extent face) := by
  exact rawCayleyWord_carrier_clear
    (faceCayleyQuaternion0 extent face)
    (faceCayleyQuaternion1 extent face)
    (faceCayleyQuaternion2 extent face)
    (faceCayleyQuaternion3 extent face)
    (faceCayleyComplement0 extent face)
    (faceCayleyComplement1 extent face)
    (faceCayleyComplement2 extent face)
    (faceCayleyComplement3 extent face)
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry0 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry1 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry2 face))
    (haarNorm_orientedCorrectedSlabLinkPolynomial extent
      (faceCayleyEntry3 face))

/-- The raw face word scalar is the global raw-scalar probe,
coefficientwise. -/
theorem faceRawCayleyWord_scalar_coeff_globalRaw
    (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (faceRawCayleyWord extent face).scalar
      (globalCayleyRawScalarPolynomial extent face) := by
  have hword := rawCayleyWordPolynomial_scalar_coeff_compiled
    (faceCayleyQuaternion0 extent face)
    (faceCayleyQuaternion1 extent face)
    (faceCayleyQuaternion2 extent face)
    (faceCayleyQuaternion3 extent face)
  have hglobal := globalCayleyRawScalarPolynomial_coeff_compiled extent face
  simpa [faceRawCayleyWord, faceCayleyQuaternion0, faceCayleyQuaternion1,
    faceCayleyQuaternion2, faceCayleyQuaternion3, faceCayleyEntry0,
    faceCayleyEntry1, faceCayleyEntry2, faceCayleyEntry3] using
      hword.trans hglobal.symm

/-- The global raw scalar is Haar-carrier equivalent to the shared global
denominator times the SAME ORIGINAL plaquette scalar. -/
theorem globalCayleyRawScalar_carrier_original
    (extent : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyRawScalarPolynomial extent face)
      (polyMul (globalCayleyDenominatorPolynomial extent face)
        (correctedSlabPlaquettePolynomial extent face).scalar) := by
  have hraw : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyRawScalarPolynomial extent face)
      (faceRawCayleyWord extent face).scalar :=
    RatPolyCoeffEqv.haarCarrier
      (faceRawCayleyWord_scalar_coeff_globalRaw extent face).symm
  have hclear := (faceRawCayleyWord_carrier_clear extent face).scalar
  have hclearedCoeff :=
    (faceClearedCayleyWord_coeff_originalPlaquette extent face).scalar
  have hscale := faceCayleyScaleProduct_coeff_globalDenominator extent face
  have hcleared : RatPolyCoeffEqv
      (faceClearedCayleyWord extent face).scalar
      (polyMul (globalCayleyDenominatorPolynomial extent face)
        (correctedSlabPlaquettePolynomial extent face).scalar) := by
    exact hclearedCoeff.trans (by
      simpa [polynomialScaleQuaternion] using
        hscale.mul (RatPolyCoeffEqv.refl
          (correctedSlabPlaquettePolynomial extent face).scalar))
  exact hraw.trans (hclear.trans (RatPolyCoeffEqv.haarCarrier hcleared))

/-- The two global division-free Cayley probes agree on the full ORIGINAL
slab Haar carrier for every later polynomial insertion. -/
theorem globalCayleyPolynomial_carrier
    (extent : Nat) (face : Z4Plaq) :
    HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (globalCayleyLeftPolynomial extent face)
      (globalCayleyDeficitPolynomial extent face) := by
  have hraw := globalCayleyRawScalar_carrier_original extent face
  have hmiddle : HaarCarrierEqv (boundaryCompleteSlabLinks extent).length
      (polyAdd
        (polyMul (polyConst 2)
          (globalCayleyDenominatorPolynomial extent face))
        (polyNeg
          (polyMul (polyConst 2)
            (polyMul (globalCayleyDenominatorPolynomial extent face)
              (correctedSlabPlaquettePolynomial extent face).scalar))))
      (polyAdd
        (polyMul (polyConst 2)
          (globalCayleyDenominatorPolynomial extent face))
        (polyNeg
          (polyMul (polyConst 2)
            (globalCayleyRawScalarPolynomial extent face)))) :=
    HaarCarrierEqv.add
      (HaarCarrierEqv.refl _ _)
      (HaarCarrierEqv.neg
        (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ _) hraw.symm))
  exact (RatPolyCoeffEqv.haarCarrier
      (globalCayleyLeftPolynomial_coeff_original extent face)).trans
    (hmiddle.trans
      (RatPolyCoeffEqv.haarCarrier
        (globalCayleyDeficitPolynomial_coeff_raw extent face)).symm)

/-- The ORIGINAL normalized slab expectation therefore identifies the two
global Cayley probes without changing the action or partition function. -/
theorem globalCayley_originalExpectation_congr
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) :
    CReal.Equiv
      (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
        (globalCayleyLeftPolynomial (centralExtent half) face))
      (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
        (globalCayleyDeficitPolynomial (centralExtent half) face)) :=
  BF4ExactSlabPolynomialExpectation.expectation_carrier_congr
    w hw0 hw1 half (globalCayleyPolynomial_carrier (centralExtent half) face)

/-- Normalized ORIGINAL expectation of the degree-two cleared Cayley term. -/
def globalCayleyOriginalDegreeTwoExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyDegreeTwoPolynomial (centralExtent half) face)

/-- Normalized ORIGINAL expectation of the degree-three cleared Cayley term. -/
def globalCayleyOriginalDegreeThreeExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyDegreeThreePolynomial (centralExtent half) face)

/-- Normalized ORIGINAL expectation of the degree-four cleared Cayley term. -/
def globalCayleyOriginalDegreeFourExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyDegreeFourPolynomial (centralExtent half) face)

/-- Normalized ORIGINAL expectation of the denominator-cleared quartic term
in the finite-Gaussian `F4` convention. -/
def globalCayleyOriginalNormalizedDegreeFourExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyNormalizedDegreeFourPolynomial (centralExtent half) face)

/-- ORIGINAL expectation of the explicit quartic denominator correction. -/
def globalCayleyOriginalQuarticNormalizationCorrectionExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyQuarticNormalizationCorrectionPolynomial
      (centralExtent half) face)

/-- The raw quartic expectation splits into the weighted normalized `F4`
expectation plus the exact denominator correction. -/
theorem globalCayley_originalDegreeFour_normalized
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) :
    CReal.Equiv
      (globalCayleyOriginalDegreeFourExpectation w hw0 hw1 half face)
      (CReal.add
        (globalCayleyOriginalNormalizedDegreeFourExpectation
          w hw0 hw1 half face)
        (globalCayleyOriginalQuarticNormalizationCorrectionExpectation
          w hw0 hw1 half face)) := by
  have hcoeff := BF4ExactSlabPolynomialExpectation.expectation_congr
    w hw0 hw1 half
      (globalCayleyDegreeFourPolynomial_coeff_normalized
        (centralExtent half) face)
  exact hcoeff.trans (by
    simpa [globalCayleyOriginalDegreeFourExpectation,
      globalCayleyOriginalNormalizedDegreeFourExpectation,
      globalCayleyOriginalQuarticNormalizationCorrectionExpectation] using
        BF4ExactSlabPolynomialExpectation.expectation_add
          w hw0 hw1 half
            (globalCayleyNormalizedDegreeFourPolynomial
              (centralExtent half) face)
            (globalCayleyQuarticNormalizationCorrectionPolynomial
              (centralExtent half) face))

/-- Normalized ORIGINAL expectation of the degree-five cleared Cayley term. -/
def globalCayleyOriginalDegreeFiveExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyDegreeFivePolynomial (centralExtent half) face)

/-- Normalized ORIGINAL expectation of the degree-six cleared Cayley term. -/
def globalCayleyOriginalDegreeSixExpectation
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) : CReal :=
  BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
    (globalCayleyDegreeSixPolynomial (centralExtent half) face)

/-- The ORIGINAL expected cleared deficit is the sum of its five named
homogeneous Cayley expectations. -/
theorem globalCayley_originalDeficit_degrees
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (face : Z4Plaq) :
    CReal.Equiv
      (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half
        (globalCayleyDeficitPolynomial (centralExtent half) face))
      (CReal.add
        (CReal.add
          (CReal.add
            (CReal.add
              (globalCayleyOriginalDegreeTwoExpectation
                w hw0 hw1 half face)
              (globalCayleyOriginalDegreeThreeExpectation
                w hw0 hw1 half face))
            (globalCayleyOriginalDegreeFourExpectation
              w hw0 hw1 half face))
          (globalCayleyOriginalDegreeFiveExpectation
            w hw0 hw1 half face))
        (globalCayleyOriginalDegreeSixExpectation
          w hw0 hw1 half face)) := by
  let extent := centralExtent half
  let p2 := globalCayleyDegreeTwoPolynomial extent face
  let p3 := globalCayleyDegreeThreePolynomial extent face
  let p4 := globalCayleyDegreeFourPolynomial extent face
  let p5 := globalCayleyDegreeFivePolynomial extent face
  let p6 := globalCayleyDegreeSixPolynomial extent face
  have hcoeff := BF4ExactSlabPolynomialExpectation.expectation_congr
    w hw0 hw1 half (globalCayleyDeficitPolynomial_coeff_degrees extent face)
  have h23 := BF4ExactSlabPolynomialExpectation.expectation_add
    w hw0 hw1 half p2 p3
  have h234 := (BF4ExactSlabPolynomialExpectation.expectation_add
    w hw0 hw1 half (polyAdd p2 p3) p4).trans
      (Pivot2.add_congr h23 (CReal.Equiv.refl _))
  have h2345 := (BF4ExactSlabPolynomialExpectation.expectation_add
    w hw0 hw1 half (polyAdd (polyAdd p2 p3) p4) p5).trans
      (Pivot2.add_congr h234 (CReal.Equiv.refl _))
  have h23456 := (BF4ExactSlabPolynomialExpectation.expectation_add
    w hw0 hw1 half (polyAdd (polyAdd (polyAdd p2 p3) p4) p5) p6).trans
      (Pivot2.add_congr h2345 (CReal.Equiv.refl _))
  simpa [extent, p2, p3, p4, p5, p6,
    globalCayleyOriginalDegreeTwoExpectation,
    globalCayleyOriginalDegreeThreeExpectation,
    globalCayleyOriginalDegreeFourExpectation,
    globalCayleyOriginalDegreeFiveExpectation,
    globalCayleyOriginalDegreeSixExpectation] using hcoeff.trans h23456

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.haarNorm_orientedCorrectedSlabLinkPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.rawCayleyWord_carrier_clear
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.faceRawCayleyWord_carrier_clear
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.faceClearedCayleyWord_coeff_scale
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.correctedSlabPlaquettePolynomial_coeff_faceCayleyQuaternionWord
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.faceClearedCayleyWord_coeff_originalPlaquette
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.faceCayleyScaleProduct_coeff_globalDenominator
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.faceRawCayleyWord_scalar_coeff_globalRaw
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.globalCayleyRawScalar_carrier_original
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.globalCayleyPolynomial_carrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.globalCayley_originalExpectation_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.globalCayley_originalDeficit_degrees
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyCarrierClear.globalCayley_originalDegreeFour_normalized
