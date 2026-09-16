/-
# Constructed positive rational-linear interior slice expectation

Every supported rational polynomial receives a computed interval certificate.
Its actual normalized middle ratios therefore have a Type-level Cauchy
witness and a returned CReal. The common finite denominator gives addition,
arbitrary signed rational homogeneity and normalization; limit uniqueness
passes them to this SAME expectation. Certified nonnegativity is retained
by every actual representative, hence in the transitive leEv order.

The expectation respects Haar-carrier equivalence and agrees with the
previous signed-source-probe time limit. This is a fixed-nome, fixed-width,
fixed-cutoff positive functional on the real supported polynomial algebra.
It is not yet a stationary cylinder law, a physical reflected OS state,
a gauge-invariant Wilson-algebra identification, or a physical mass gap.
-/

import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
import YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit
import YMGap.Continuum.ContinuousFunctionalCalculusForm

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialMiddleTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Actual diagonal Cauchy witness for EVERY supported polynomial; its cap
and modulus are computed from the supplied polynomial, not assumed. -/
def polynomialCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p) :
    QCauchy (fun t => middleRatio hw0 hw1 K width hK t t p) :=
  intervalMiddleCauchy hw0 hw1 K width hK (polynomialInterval (N width) p hp)

/-- The complete explicit time modulus, independent of late heat cutoff. -/
theorem polynomialCauchy_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p) (epsilon : Q') :
    (polynomialCauchy hw0 hw1 K width hK p hp).M epsilon =
      intervalMiddleModulus hw0 hw1 width (polynomialCap p) epsilon := rfl

/-- The positive linear expectation constructed from the original messages. -/
def expectation {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p) : CReal :=
  ofQ'CauchySeq _ (polynomialCauchy hw0 hw1 K width hK p hp)

theorem expectation_converges {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p) :
    ConvergesTo (fun t => ofQ' (middleRatio hw0 hw1 K width hK t t p))
      (expectation hw0 hw1 K width hK p hp) :=
  convergesTo_ofQ'CauchySeq _ (polynomialCauchy hw0 hw1 K width hK p hp)

-- The polynomial compiler is finite data; use its proved API, not expansion.
attribute [local irreducible] polynomialCauchy baseLinks middleRatio

/-- Normalization holds for every actual representative, not only asymptotically. -/
theorem expectation_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) :
    Equiv (expectation hw0 hw1 K width hK polyOne (supported_one _)) (ofQ' 1) :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    middleRatio_one hw0 hw1 K width hK
      (QMhat _ (polynomialCauchy hw0 hw1 K width hK polyOne (supported_one _)) k)
      (QMhat _ (polynomialCauchy hw0 hw1 K width hK polyOne (supported_one _)) k))

/-- Addition is preserved on the full supported polynomial algebra, even
though the two inputs and their sum have different computed moduli. -/
theorem expectation_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (hq : SupportedQuaternionBlocks (N width) q) :
    Equiv (expectation hw0 hw1 K width hK (polyAdd p q) (supported_add hp hq))
      (add (expectation hw0 hw1 K width hK p hp) (expectation hw0 hw1 K width hK q hq)) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ => middleRatio_add hw0 hw1 K width hK t t p q))
    (expectation_converges hw0 hw1 K width hK (polyAdd p q) (supported_add hp hq))
    (TrigAddCReal.convergesTo_add (expectation_converges hw0 hw1 K width hK p hp)
      (expectation_converges hw0 hw1 K width hK q hq))

/-- Rational homogeneity includes negative coefficients; no positivity of
the scale, modulus monotonicity or regular-real conversion is assumed. -/
theorem expectation_smul {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    Equiv (expectation hw0 hw1 K width hK (polySmul c p) (support_smul hp c))
      (mul (ofQ' c) (expectation hw0 hw1 K width hK p hp)) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ => middleRatio_smul hw0 hw1 K width hK t t c p))
    (expectation_converges hw0 hw1 K width hK (polySmul c p) (support_smul hp c))
    (convergesTo_constMul c (expectation_converges hw0 hw1 K width hK p hp))

/-- Coefficient recoding cannot change this expectation. -/
theorem expectation_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (hq : SupportedQuaternionBlocks (N width) q)
    (h : RatPolyCoeffEqv p q) :
    Equiv (expectation hw0 hw1 K width hK p hp) (expectation hw0 hw1 K width hK q hq) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv (fun _ => middleRatio_congr hw0 hw1 K width hK t t h))
    (expectation_converges hw0 hw1 K width hK p hp)
    (expectation_converges hw0 hw1 K width hK q hq)

/-- Equality under arbitrary Haar insertion survives the original limiting
messages. This retains the original sphere/carrier relations. -/
theorem expectation_carrier_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (hq : SupportedQuaternionBlocks (N width) q)
    (h : HaarCarrierEqv (N width) p q) :
    Equiv (expectation hw0 hw1 K width hK p hp) (expectation hw0 hw1 K width hK q hq) :=
  Equiv_of_limit_of_equal
    (fun t => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => middleRatio_carrier_congr hw0 hw1 K width hK t t h))
    (expectation_converges hw0 hw1 K width hK p hp)
    (expectation_converges hw0 hw1 K width hK q hq)

/-- Positivity is proved in the transitive eventual order from each actual
representative's finite certificate, with no abstract positive-state premise. -/
theorem expectation_certificate_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (P : Certificate (N width) p) :
    leEv (ofQ' 0) (expectation hw0 hw1 K width hK p hp) :=
  leEv_ofQ'_of_approx_ge (fun k =>
    middleRatio_certificate_nonnegative hw0 hw1 K width hK
      (QMhat _ (polynomialCauchy hw0 hw1 K width hK p hp) k)
      (QMhat _ (polynomialCauchy hw0 hw1 K width hK p hp) k) P)

/-- The positive-functional square law on every supported real polynomial. -/
theorem expectation_square_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) :
    leEv (ofQ' 0) (expectation hw0 hw1 K width hK (polyMul p p) (supported_polyMul hp hp)) :=
  expectation_certificate_nonnegative hw0 hw1 K width hK (supported_polyMul hp hp) (.square p hp)

/-- The new algebra functional agrees with the already constructed source-
probe limit. With the previous physical-face pin this is the original scalar. -/
theorem expectation_sourceProbe {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (fs : List FaceFactor) :
    Equiv (expectation hw0 hw1 K width hK (sourceProbe width fs) (sourceProbe_supported width fs))
      (middleTimeLimit hw0 hw1 K width hK fs) :=
  Equiv_of_limit_of_equal (fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))
    (expectation_converges hw0 hw1 K width hK (sourceProbe width fs) (sourceProbe_supported width fs))
    (middleTime_converges hw0 hw1 K width hK fs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.polynomialCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.polynomialCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation_smul
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation_carrier_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation_certificate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation_square_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPolynomialState.expectation_sourceProbe
