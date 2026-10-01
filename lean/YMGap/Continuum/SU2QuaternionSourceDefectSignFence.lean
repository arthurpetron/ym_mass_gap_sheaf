/-
# Both signs of the centered source-norm defect on the actual one-link heat

The two sources are positive certificates on the quaternion carrier. Their
centers are computed from their own q*P(q) densities. This finite fence does
not identify either source with a four-dimensional terminal message.
-/

import YMGap.Continuum.SU2QuaternionPositiveSourceVarianceFence
import YMGap.Continuum.SU2QuaternionProductHeatCenteredMixed
import YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.SU2QuaternionSourceDefectSignFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress (Dir4)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_coordinate)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionProductHeatWilsonWord
open YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence
  (half fundamental fundamental_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.SU2QuaternionHalfHeatThreeCertificate
  (heatAt_half_three_quarterFloor)

local infix:50 " ≈ " => Q'.eqv

private def quarter : Q' := Q'.mkPos 1 4 (by decide)
private def threeQuarters : Q' := Q'.mkPos 3 4 (by decide)

/-- The one-link spin-two mode, exactly `fundamental² - 1` on SU(2). -/
def spinTwo : RatPoly :=
  characterPolynomial (PolyQuaternion.coordinateVariable 0).scalar 2

def sourcePlus : RatPoly := polyAdd polyOne (polySmul quarter spinTwo)
def sourceMinus : RatPoly := polyAdd polyOne (polySmul (-quarter) spinTwo)

theorem sourcePlus_supported : SupportedQuaternionBlocks 1 sourcePlus :=
  supported_add (supported_one 1)
    (polySmul_supported
      (character_supported (coordinate_supported (by decide : 0 < 1) (0 : Fin 4)) 2)
      quarter)

theorem sourceMinus_supported : SupportedQuaternionBlocks 1 sourceMinus :=
  supported_add (supported_one 1)
    (polySmul_supported
      (character_supported (coordinate_supported (by decide : 0 < 1) (0 : Fin 4)) 2)
      (-quarter))

private def fundamentalSquareBound : SquareBound 1 fundamental 4 := by
  let coordinate := PolyQuaternion.coordinateVariable 0
  let B := (SquareBound.scalar (Supported.coordinate (by decide : 0 < 1))
    (haarNorm_coordinate (by decide : 0 < 1))).smul 2
  exact SquareBound.ofCoeff fundamental_supported
    (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (B.changeCap (by decide))

/-- `1 + χ₂/4 = 3/4 + χ₁²/4`, with both summands certified. -/
def sourcePlusCertificate : Certificate 1 sourcePlus :=
  .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.add (.constant 1 threeQuarters (by decide))
      (.smul quarter (by decide) (.square fundamental fundamental_supported)))

/-- `1 - χ₂/4 = 1/4 + (4-χ₁²)/4`; the unit-quaternion
four-square certificate proves positivity, including arbitrary insertions. -/
def sourceMinusCertificate : Certificate 1 sourceMinus :=
  .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.add (.constant 1 quarter (by decide))
      (.smul quarter (by decide) fundamentalSquareBound.certificate))

/-- The actual one-link full product map has the bare fundamental eigenpin
under every supported insertion. It is not an interacting-source eigenpin. -/
theorem fundamental_eigenpin :
    SupportedHaarEqv 1 (productMap 1 half 3 [0] fundamental)
      (polySmul (qpow half 3) fundamental) := by
  let letter : OrientedBF4Link := ⟨((0,0,0,0), Dir4.x0), false⟩
  let block : OrientedBF4Link → Nat := fun _ => 0
  let wordFundamental := characterPolynomial (wordAt block [letter]).scalar 1
  have hshape : RatPolyCoeffEqv fundamental wordFundamental :=
    RatPolyCoeffEqv.of_canon_termwise (by decide)
  have hword := productMap_fundamental_word 1 half 3 (by decide)
    block [letter] [0] (by decide) (by decide) (by decide)
    (fun _ _ => List.mem_cons_self)
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
    (productMap_congr 1 half 3 [0] hshape))).trans
      (hword.trans (SupportedHaarEqv.of_carrier
        (RatPolyCoeffEqv.haarCarrier (hshape.symm.smul (qpow half 3)))))

/-- The very same finite product heat has a strict positive quarter floor. -/
def heatQuarterFloor : Certificate 2
    (polyAdd (heatAt 0 1 half 3)
      (polyNeg (cap quarter))) :=
  heatAt_half_three_quarterFloor

/-- The original interacting one-slice density for any source. -/
def sourceDensity (q : RatPoly) : RatPoly :=
  polyMul q (productMap 1 half 3 [0] q)

def sourceMass (q : RatPoly) : Q' := quaternionHaar 1 (sourceDensity q)
def sourceFirst (q : RatPoly) : Q' :=
  quaternionHaar 1 (polyMul (sourceDensity q) fundamental)
def sourceSecond (q : RatPoly) : Q' :=
  quaternionHaar 1 (polyMul (sourceDensity q) (polyMul fundamental fundamental))

set_option maxRecDepth 100000 in
theorem plusMass_value : sourceMass sourcePlus ≈ Q'.mkPos 4097 4096 (by decide) := by decide

set_option maxRecDepth 100000 in
theorem minusMass_value : sourceMass sourceMinus ≈ Q'.mkPos 4097 4096 (by decide) := by decide

set_option maxRecDepth 100000 in
theorem plusFirst_zero : sourceFirst sourcePlus ≈ 0 := by decide

set_option maxRecDepth 100000 in
theorem minusFirst_zero : sourceFirst sourceMinus ≈ 0 := by decide

set_option maxRecDepth 100000 in
theorem plusSecond_value : sourceSecond sourcePlus ≈ Q'.mkPos 2563 2048 (by decide) := by decide

set_option maxRecDepth 100000 in
theorem minusSecond_value : sourceSecond sourceMinus ≈ Q'.mkPos 1535 2048 (by decide) := by decide

private theorem positive_of_eqv {a b : Q'} (h : a ≈ b) (hb : (0 : Q') < b) :
    (0 : Q') < a := by
  have hn : ¬ a ≤ (0 : Q') := by
    intro ha
    exact (Int.not_le.mpr hb) (Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) ha)
  exact Int.not_le.mp hn

theorem plusMass_positive : (0 : Q') < sourceMass sourcePlus :=
  positive_of_eqv plusMass_value (by decide)

theorem minusMass_positive : (0 : Q') < sourceMass sourceMinus :=
  positive_of_eqv minusMass_value (by decide)

/-- This is the actual q*P(q) center, not the bare Haar mean. -/
def sourceCenter (q : RatPoly) (h : (0 : Q') < sourceMass q) : Q' :=
  normalizedMoment 1 (sourceDensity q) fundamental h

theorem plusCenter_zero : sourceCenter sourcePlus plusMass_positive ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ plusFirst_zero)
    (Q'.zero_mul_eqv _)

theorem minusCenter_zero : sourceCenter sourceMinus minusMass_positive ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ minusFirst_zero)
    (Q'.zero_mul_eqv _)

/-- Normalized variance uses the same q*P(q) source density and center. -/
def sourceVariance (q : RatPoly) (h : (0 : Q') < sourceMass q) : Q' :=
  normalizedVariance 1 (sourceDensity q) fundamental h

set_option maxRecDepth 100000 in
theorem plusVariance_value :
    sourceVariance sourcePlus plusMass_positive ≈ Q'.mkPos 5126 4097 (by decide) := by decide

set_option maxRecDepth 100000 in
theorem minusVariance_value :
    sourceVariance sourceMinus minusMass_positive ≈ Q'.mkPos 3070 4097 (by decide) := by decide

theorem plusVariance_positive : (0 : Q') < sourceVariance sourcePlus plusMass_positive :=
  positive_of_eqv plusVariance_value (by decide)

theorem minusVariance_positive : (0 : Q') < sourceVariance sourceMinus minusMass_positive :=
  positive_of_eqv minusVariance_value (by decide)

/-- The same signed defect expression as `sourceNormDefect`, with a source's
own original q*P(q) center. Here the fundamental eigenvalue is `(1/2)^3`. -/
def sourceNormDefect1 (q : RatPoly) (h : (0 : Q') < sourceMass q) : Q' :=
  let c := sourceCenter q h
  let psi := shifted fundamental c
  let lambda := qpow half 3
  lambda * sourceCorrection 1 half 3 [0] q psi +
    (1-lambda)*c*quaternionHaar 1 (polyMul (polyMul q q) psi)

private theorem centered_defect_eq_raw (q : RatPoly)
    (h : (0 : Q') < sourceMass q)
    (hc : sourceCenter q h ≈ 0) :
    sourceNormDefect1 q h ≈
      (qpow half 3) * sourceCorrection 1 half 3 [0] q fundamental := by
  let c := sourceCenter q h
  let psi := shifted fundamental c
  let lambda := qpow half 3
  have hz : -c ≈ 0 := Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _ hc) (by decide : -(0 : Q') ≈ 0)
  have hpsi : RatPolyCoeffEqv psi fundamental := by
    unfold psi shifted
    exact ((RatPolyCoeffEqv.one_smul fundamental).add
      (RatPolyCoeffEqv.smul_coefficient hz polyOne)).trans
      (((RatPolyCoeffEqv.refl fundamental).add
        (RatPolyCoeffEqv.zero_smul polyOne)).trans
        (RatPolyCoeffEqv.add_zero fundamental))
  have hC : sourceCorrection 1 half 3 [0] q psi ≈
      sourceCorrection 1 half 3 [0] q fundamental := by
    unfold sourceCorrection
    exact haar_of_coeff
      (((RatPolyCoeffEqv.refl q).mul (hpsi.mul hpsi)).mul_right
        (polyAdd (productMap 1 half 3 [0] q) (polyNeg q)))
  have hzero : ((1-lambda)*c) *
      quaternionHaar 1 (polyMul (polyMul q q) psi) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (1-lambda) _ _ hc)
          (Q'.mul_zero_eqv _)))
      (Q'.zero_mul_eqv _)
  unfold sourceNormDefect1
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left lambda _ _ hC) hzero)
    (Q'.eqv_of_eq (Q'.add_zero' _))

def rawCorrection (q : RatPoly) : Q' :=
  sourceCorrection 1 half 3 [0] q fundamental

set_option maxRecDepth 100000 in
theorem plusRawCorrection_value :
    rawCorrection sourcePlus ≈ -(Q'.mkPos 765 2048 (by decide)) := by decide

set_option maxRecDepth 100000 in
theorem minusRawCorrection_value :
    rawCorrection sourceMinus ≈ Q'.mkPos 255 2048 (by decide) := by decide

theorem plusDefect_value :
    sourceNormDefect1 sourcePlus plusMass_positive ≈
      -(Q'.mkPos 765 16384 (by decide)) :=
  Q'.eqv_trans _ _ _ (centered_defect_eq_raw sourcePlus plusMass_positive plusCenter_zero)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (qpow half 3) _ _ plusRawCorrection_value)
      (by decide))

theorem minusDefect_value :
    sourceNormDefect1 sourceMinus minusMass_positive ≈
      Q'.mkPos 255 16384 (by decide) :=
  Q'.eqv_trans _ _ _ (centered_defect_eq_raw sourceMinus minusMass_positive minusCenter_zero)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (qpow half 3) _ _ minusRawCorrection_value)
      (by decide))

theorem plusDefect_negative : sourceNormDefect1 sourcePlus plusMass_positive < 0 :=
  Q'.lt_of_le_of_lt (Q'.le_of_eqv plusDefect_value)
    (by decide : -(Q'.mkPos 765 16384 (by decide)) < (0 : Q'))

theorem minusDefect_positive : (0 : Q') < sourceNormDefect1 sourceMinus minusMass_positive :=
  positive_of_eqv minusDefect_value (by decide)

/-- Neither universal sign follows from positive sources, the bare heat
eigenpin, and positive variance under each source's own q*P(q) law. -/
theorem universal_nonnegative_defect_false :
    ¬ (∀ (q : RatPoly) (_Q : Certificate 1 q)
      (h : (0 : Q') < sourceMass q),
      (0 : Q') < sourceVariance q h → (0 : Q') ≤ sourceNormDefect1 q h) := by
  intro h
  exact (Int.not_le.mpr plusDefect_negative)
    (h sourcePlus sourcePlusCertificate plusMass_positive plusVariance_positive)

theorem universal_nonpositive_defect_false :
    ¬ (∀ (q : RatPoly) (_Q : Certificate 1 q)
      (h : (0 : Q') < sourceMass q),
      (0 : Q') < sourceVariance q h → sourceNormDefect1 q h ≤ (0 : Q')) := by
  intro h
  exact (Int.not_le.mpr minusDefect_positive)
    (h sourceMinus sourceMinusCertificate minusMass_positive minusVariance_positive)

#print axioms sourcePlusCertificate
#print axioms sourceMinusCertificate
#print axioms fundamental_eigenpin
#print axioms heatQuarterFloor
#print axioms plusMass_value
#print axioms minusMass_value
#print axioms plusFirst_zero
#print axioms minusFirst_zero
#print axioms plusSecond_value
#print axioms minusSecond_value
#print axioms plusCenter_zero
#print axioms minusCenter_zero
#print axioms plusVariance_value
#print axioms minusVariance_value
#print axioms plusVariance_positive
#print axioms minusVariance_positive
#print axioms plusRawCorrection_value
#print axioms minusRawCorrection_value
#print axioms plusDefect_value
#print axioms minusDefect_value
#print axioms plusDefect_negative
#print axioms minusDefect_positive
#print axioms universal_nonnegative_defect_false
#print axioms universal_nonpositive_defect_false

end YMGap.Continuum.SU2QuaternionSourceDefectSignFence
