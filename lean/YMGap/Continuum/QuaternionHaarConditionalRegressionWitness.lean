/-
# A one-head positive-source regression mismatch

For the original one-quaternion Haar law with unit insertion, the positive
incoming polynomial `2+x₀` and constant second input give a nonzero
determinant residual `U*b-A*C`. Thus U*J is strictly larger than the
Gram-only term `A^2*(U*H[c^2]-C^2)`. This is only a finite Haar witness, not an
original Yang--Mills terminal message or a claim about the full score budget.
-/

import YMGap.Continuum.QuaternionHaarUnitScalarSquare
import YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
import YMGap.Continuum.SU2QuaternionAngularDerivative
import YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.SU2QuaternionRelativeHeatAngularInvariant
import YMGap.Continuum.SU2QuaternionProductHeatPositive

namespace YMGap.Continuum.QuaternionHaarConditionalRegressionWitness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (PolyQuaternion)
open YMGap.Continuum.QuaternionHaarSquareCertificate (Certificate)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
  (oneAddScalar oneAddScalar_certificate)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_coordinate)

local infix:50 " ≈ " => Q'.eqv

/-- The positive incoming polynomial `2+x₀` on one original quaternion head. -/
def incoming : RatPoly :=
  polyAdd polyOne (oneAddScalar (PolyQuaternion.coordinateVariable 0))

/-- Constant second input, with the same one-head unit Haar insertion. -/
def reference : RatPoly := polyOne

/-- An actual original-Haar positivity certificate for the incoming source. -/
def incoming_certificate : Certificate 1 incoming :=
  Certificate.add (Certificate.one 1)
    (oneAddScalar_certificate
      (QuaternionHaarUnitScalarSquare.Supported.coordinate (by decide))
      (haarNorm_coordinate (by decide)))

/-- Explicit unit floor, stronger than mere incoming nonnegativity. -/
def incoming_floor_certificate : Certificate 1 (polyAdd incoming (polyNeg polyOne)) :=
  Certificate.ofCoeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => polyOne | _ => oneAddScalar (PolyQuaternion.coordinateVariable 0)))
    (oneAddScalar_certificate
      (QuaternionHaarUnitScalarSquare.Supported.coordinate (by decide))
      (haarNorm_coordinate (by decide)))

def headMean : Q' := quaternionHaar 1 incoming
def referenceMean : Q' := quaternionHaar 1 reference
def headSecond : Q' := quaternionHaar 1 (polyMul incoming incoming)
def crossMoment : Q' := quaternionHaar 1 (polyMul incoming reference)
def referenceSecond : Q' := quaternionHaar 1 (polyMul reference reference)

/-- The one-head Gram determinant for the two columns. -/
def gram : Q' := headSecond * referenceSecond - crossMoment * crossMoment

/-- The determinant residual appearing in the conditional regression. -/
def residual : Q' := headSecond * referenceMean - headMean * crossMoment

/-- J is the literal paired square, not an alias of the mismatch E. -/
def pairedSquare : Q' :=
  let X := polyAdd (polySmul headMean reference)
    (polyNeg (polySmul referenceMean incoming))
  quaternionHaar 1 (polyMul X X)

theorem original_haar_moments :
    headMean ≈ 2 ∧ referenceMean ≈ 1 ∧
    headSecond ≈ Q'.mkPos 17 4 (by decide) ∧ crossMoment ≈ 2 ∧
    referenceSecond ≈ 1 := by
  decide

theorem gram_exact : gram ≈ Q'.mkPos 1 4 (by decide) := by
  decide

theorem residual_exact : residual ≈ Q'.mkPos 1 4 (by decide) := by
  decide

theorem pairedSquare_exact : pairedSquare ≈ Q'.mkPos 1 4 (by decide) := by
  decide

theorem residual_square_exact : residual*residual ≈ Q'.mkPos 1 16 (by decide) := by
  decide

/-- Even with a positive incoming source, the regression residual is not
automatically omitted from the paired-square regression. -/
theorem regression_gram_mismatch :
    headSecond * pairedSquare > headMean * headMean * gram := by
  decide

#print axioms incoming
#print axioms reference
#print axioms incoming_certificate
#print axioms incoming_floor_certificate
#print axioms headMean
#print axioms referenceMean
#print axioms headSecond
#print axioms crossMoment
#print axioms referenceSecond
#print axioms gram
#print axioms residual
#print axioms pairedSquare
#print axioms original_haar_moments
#print axioms gram_exact
#print axioms residual_exact
#print axioms pairedSquare_exact
#print axioms residual_square_exact
#print axioms regression_gram_mismatch

/-! ## Auxiliary two-head score-sign test

This bounded polynomial model probes the sign of the complete centered Ward
term. It has two independent unit-quaternion Haar heads and is not a BF4
action, a local gauge-theory realization, or a physical mass-gap statement.
The two scalar sources are class polynomials; no new formal conjugation
invariance theorem or original-action identification is asserted here. -/

namespace ScoreSign

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Continuum.SU2QuaternionAngularDerivative (angularDerivative)
open YMGap.Continuum.SU2QuaternionAngularSupport
  (angularDerivative_one angularDerivative_smul)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.SU2QuaternionRelativeHeatAngularInvariant
  (pairedAt scalarAt_pairedAngular_carrier_at)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal (partialHaarHeads)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer (canonRat ratWeightedSum_canon)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
  (haarNorm_mul polyQuaternionNorm_conj)

private def half : Q' := Q'.mkPos 1 2 (by decide)
private def eighth : Q' := Q'.mkPos 1 8 (by decide)
private def sevenEighths : Q' := Q'.mkPos 7 8 (by decide)
private def sevenThirtySeconds : Q' := Q'.mkPos 7 32 (by decide)
private def quarter : Q' := Q'.mkPos 1 4 (by decide)

def x : PolyQuaternion := PolyQuaternion.coordinateVariable 0
def y : PolyQuaternion := PolyQuaternion.coordinateVariable 1
def z : PolyQuaternion := PolyQuaternion.mul x (PolyQuaternion.conj y)

/-- The scalar of `x * conj y` is the four-coordinate dot product. -/
def K : RatPoly := polyAdd polyOne (polySmul half z.scalar)
def g : RatPoly := polyAdd polyOne (polySmul sevenEighths x.scalar)
def W : RatPoly := polyMul K g

/-- The first quaternion is integrated; the second remains the boundary.
Canonicalization only combines exact rational coefficients. -/
def A : RatPoly := canonRat (partialHaarHeads 1 W)
def phi (c : Nat) : RatPoly :=
  if c == 0 then
    polyAdd x.scalar (polyNeg (polySmul sevenThirtySeconds polyOne))
  else
    polyAdd (polyMul x.scalar x.scalar) (polyNeg (polySmul quarter polyOne))
def B (c : Nat) : RatPoly := canonRat (partialHaarHeads 1 (polyMul W (phi c)))
def C (c : Nat) : RatPoly :=
  canonRat (partialHaarHeads 1 (polyMul W (polyMul (phi c) (phi c))))
def nu (c : Nat) : RatPoly :=
  canonRat (polyAdd (polyMul A (C c)) (polyNeg (polyMul (B c) (B c))))
def X (c : Nat) : RatPoly :=
  canonRat (polyAdd (polyMul (liftBoundary 1 A) (phi c))
    (polyNeg (liftBoundary 1 (B c))))

/-- Actual outgoing derivative and actual incoming tilt. -/
def D (i j : Nat) : RatPoly := canonRat (angularDerivative i j A)
def tilt (i j : Nat) : RatPoly :=
  canonRat (polyMul K (angularDerivative i j g))
def noise (c i j : Nat) : RatPoly :=
  canonRat (partialHaarHeads 1 (polyMul (tilt i j) (polyMul (X c) (X c))))

/-- The literal first finite positive-window reciprocal, whose scale is 1/2. -/
def G : RatPoly := reciprocal A 2 (by decide) 1
def V : RatPoly := polyOne

def pairScore (c i j : Nat) : Q' :=
  quaternionHaar 1 (polyMul
    (polyMul (polyMul (polyMul V V) (polyMul G G)) (D i j))
    (polyAdd (noise c i j) (polyNeg (polyMul (nu c) (D i j)))))

/-- Same score with its positive reciprocal square omitted, for auditing. -/
def barePairScore (c i j : Nat) : Q' :=
  quaternionHaar 1 (polyMul (D i j)
    (polyAdd (noise c i j) (polyNeg (polyMul (nu c) (D i j)))))

def total (c : Nat) : Q' :=
  pairScore c 0 1 + pairScore c 0 2 + pairScore c 0 3 +
  pairScore c 1 2 + pairScore c 1 3 + pairScore c 2 3

def bareTotal (c : Nat) : Q' :=
  barePairScore c 0 1 + barePairScore c 0 2 + barePairScore c 0 3 +
  barePairScore c 1 2 + barePairScore c 1 3 + barePairScore c 2 3

/-- The two-head source has unit global Haar mass and the chosen first
coordinate is exactly globally centered. -/
theorem source_mass_and_centering :
    quaternionHaar 2 W ≈ 1 ∧
    quaternionHaar 2 (polyMul W (phi 0)) ≈ 0 ∧
    quaternionHaar 2 (polyMul W (phi 1)) ≈ 0 := by
  decide

/-- Normalization preserves every coefficient probe, so these are the
actual integrated moments rather than independently supplied values. -/
theorem moments_are_actual (c : Nat) :
    RatPolyCoeffEqv A (partialHaarHeads 1 W) ∧
    RatPolyCoeffEqv (B c) (partialHaarHeads 1 (polyMul W (phi c))) ∧
    RatPolyCoeffEqv (C c)
      (partialHaarHeads 1 (polyMul W (polyMul (phi c) (phi c)))) := by
  constructor
  · intro weight
    exact ratWeightedSum_canon weight _
  constructor
  · intro weight
    exact ratWeightedSum_canon weight _
  · intro weight
    exact ratWeightedSum_canon weight _

/-- The evaluated derivative, tilt and noise retain their literal input
polynomials through exact coefficient normalization. -/
theorem score_inputs_are_actual (c i j : Nat) :
    RatPolyCoeffEqv (D i j) (angularDerivative i j A) ∧
    RatPolyCoeffEqv (tilt i j) (polyMul K (angularDerivative i j g)) ∧
    RatPolyCoeffEqv (noise c i j)
      (partialHaarHeads 1 (polyMul (tilt i j) (polyMul (X c) (X c)))) := by
  constructor
  · intro weight
    exact ratWeightedSum_canon weight _
  constructor
  · intro weight
    exact ratWeightedSum_canon weight _
  · intro weight
    exact ratWeightedSum_canon weight _

/-- Exact outgoing boundary density after integrating the first head. -/
theorem boundary_density :
    RatPolyCoeffEqv A
      (polyAdd polyOne (polySmul (Q'.mkPos 7 64 (by decide)) (polyVar 0))) := by
  exact RatPolyCoeffEqv.of_canon_termwise (by decide)

/-- The literal degree-one reciprocal equals the constant half polynomial. -/
theorem reciprocal_one : RatPolyCoeffEqv G (polySmul half polyOne) := by
  exact RatPolyCoeffEqv.of_canon_termwise (by decide)

/-- The simultaneous quaternion rotation leaves the coupling invariant on
the actual Haar carrier; arbitrary raw exponent-list probes distinguish
trailing-zero padding and are not the equality asserted here. -/
theorem coupling_pair_invariant (i j : Nat) (hi : i < 4) (hj : j < 4) :
    HaarCarrierEqv 2
      (polyAdd (angularDerivative i j K) (angularDerivative (i+4) (j+4) K))
      polyZero := by
  have hd (u v : Nat) : RatPolyCoeffEqv (angularDerivative u v K)
      (polySmul half (angularDerivative u v z.scalar)) :=
    (YMGap.Continuum.SU2QuaternionAngularDerivative.angularDerivative_add
      u v polyOne (polySmul half z.scalar)).trans
      (((angularDerivative_one u v).add
        (angularDerivative_smul u v half z.scalar)).trans
          (RatPolyCoeffEqv.zero_add _))
  have hz : HaarCarrierEqv 2
      (polyAdd (angularDerivative i j z.scalar)
        (angularDerivative (i+4) (j+4) z.scalar)) polyZero := by
    simpa only [pairedAt, Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.add_comm]
      using scalarAt_pairedAngular_carrier_at 2 0 1 i j
        (by decide) (by decide) (by decide) hi hj
  exact (RatPolyCoeffEqv.haarCarrier
    (((hd i j).add (hd (i+4) (j+4))).trans
      (RatPolyCoeffEqv.smul_add half _ _).symm)).trans
        ((HaarCarrierEqv.smul half hz).trans
          (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_zero half)))

/-- Unit-quaternion norm of the conjugated product supplies the positive
dot-product factor on the original two-head Haar carrier. -/
def dot_certificate : Certificate 2 (oneAddScalar z) :=
  oneAddScalar_certificate
    ((QuaternionHaarUnitScalarSquare.Supported.coordinate (by decide)).mul
      ((QuaternionHaarUnitScalarSquare.Supported.coordinate (by decide)).conj))
    (haarNorm_mul (haarNorm_coordinate (by decide))
      ((RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj y)).trans
        (haarNorm_coordinate (by decide))))

/-- `K - 1/2 = (1/2)(1+scalar(x*conj y))`. -/
def coupling_floor_certificate :
    Certificate 2 (polyAdd K (polyNeg (polySmul half polyOne))) :=
  Certificate.ofCoeff
    (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.smul half (by decide) dot_certificate)

/-- `g - 1/8 = (7/8)(1+x₀)`. -/
def incoming_floor_certificate :
    Certificate 2 (polyAdd g (polyNeg (polySmul eighth polyOne))) :=
  Certificate.ofCoeff
    (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.smul sevenEighths (by decide)
      (oneAddScalar_certificate (p := x)
        (QuaternionHaarUnitScalarSquare.Supported.coordinate (block := 0) (by decide))
        (haarNorm_coordinate (block := 0) (by decide))))

/-- Explicit strict floor `W >= 1/16` under the original product Haar law. -/
def source_floor_certificate :
    Certificate 2
      (polyAdd W (polyNeg (polySmul (Q'.mkPos 1 16 (by decide)) polyOne))) := by
  let gCert : Certificate 2 g :=
    Certificate.ofCoeff
      (RatPolyCoeffEqv.of_canon_termwise (by decide))
      (incoming_floor_certificate.add (Certificate.constant 2 eighth (by decide)))
  let source := coupling_floor_certificate.mul gCert |>.add
    ((Certificate.constant 2 half (by decide)).mul incoming_floor_certificate)
  exact Certificate.ofCoeff
    (RatPolyCoeffEqv.of_canon_termwise (by decide)) source

/-- A positive finite score for one globally centered coordinate. -/
theorem total_phi0_exact :
    total 0 ≈ Q'.mkPos 61103 1610612736 (by decide) := by
  decide

/-- A negative finite score for the globally centered scalar square. -/
theorem total_phi1_exact :
    total 1 ≈ -(Q'.mkPos 298655 6442450944 (by decide)) := by
  decide

theorem bare_totals_exact :
    bareTotal 0 ≈ Q'.mkPos 61103 402653184 (by decide) ∧
    bareTotal 1 ≈ -(Q'.mkPos 298655 1610612736 (by decide)) := by
  decide

theorem score_signs : (0 : Q') < total 0 ∧ total 1 < (0 : Q') := by
  decide

#print axioms source_mass_and_centering
#print axioms moments_are_actual
#print axioms score_inputs_are_actual
#print axioms boundary_density
#print axioms reciprocal_one
#print axioms coupling_pair_invariant
#print axioms dot_certificate
#print axioms coupling_floor_certificate
#print axioms incoming_floor_certificate
#print axioms source_floor_certificate
#print axioms total_phi0_exact
#print axioms total_phi1_exact
#print axioms bare_totals_exact
#print axioms score_signs

end ScoreSign

/-! ## Auxiliary one-link heat alignment-energy test

The actual cutoff-one SU(2) character heat factor at nome `1/2` produces a
positive quadratic alignment residual. Its mixed-minus-diagonal energy on a
centered coordinate is negative. This is a finite one-link kinetic diagnostic,
not a BF4 action, a physical Wilson observable, or a mass-gap counterexample. -/

namespace AlignmentEnergy

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (heatAt scalarAt)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)
open YMGap.Continuum.SU2QuaternionProductHeatPositive
  (haarQuadratic insertion insertion_coeff insertion_add insertion_smul
    character_insertion_nonnegative productHeat_quadratic_nonnegative)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)

private def w : Q' := Q'.mkPos 1 2 (by decide)
private def half : Q' := Q'.mkPos 1 2 (by decide)
private def wCubed : Q' := w^3
private def cOne : Q' := Q'.mkPos 15 32 (by decide)
private def cTwo : Q' := Q'.mkPos 1 8 (by decide)

/-- Literal cutoff-one heat character factor on the two quaternion heads. -/
def K : RatPoly := heatAt 0 1 w 1
def scalar : RatPoly := scalarAt 1 0
def R : RatPoly :=
  polyMul K (polyAdd scalar (polyNeg (polySmul wCubed polyOne)))

/-- The literal heat packet reduces to `1 + scalar/2` at this nome and cutoff. -/
theorem heat_kernel_pin :
    RatPolyCoeffEqv K (polyAdd polyOne (polySmul half (scalarAt 0 1))) := by
  exact RatPolyCoeffEqv.of_canon_termwise (by decide)

theorem scalar_pair_pin : RatPolyCoeffEqv scalar (scalarAt 0 1) := by
  exact RatPolyCoeffEqv.of_canon_termwise (by decide)

/-- The same residual is a positive combination of the genuine first two
relative characters. This is a coefficient identity, not a positivity axiom. -/
theorem residual_character_pin :
    RatPolyCoeffEqv R
      (polyAdd (polySmul cOne (characterPolynomial scalar 1))
        (polySmul cTwo (characterPolynomial scalar 2))) := by
  exact RatPolyCoeffEqv.of_canon_termwise (by decide)

/-- The actual heat factor has the explicit strict half-floor certificate. -/
def heat_floor_certificate :
    Certificate 2 (polyAdd K (polyNeg (polySmul half polyOne))) :=
  Certificate.ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
    ScoreSign.coupling_floor_certificate

/-- The residual is PSD as a two-head Haar quadratic for every supported,
possibly signed, one-head polynomial. -/
theorem residual_quadratic_nonnegative (p : RatPoly)
    (hp : SupportedQuaternionBlocks 1 p) :
    (0 : Q') ≤ insertion 1 polyOne p R := by
  have hbase : ∀ q, SupportedQuaternionBlocks 1 q →
      (0 : Q') ≤ haarQuadratic 1 polyOne q := by
    intro q hq
    simpa [YMGap.Continuum.SU2QuaternionProductHeatMarginals.productHeat,
      YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization.polynomialProduct]
      using (productHeat_quadratic_nonnegative 1 w (by decide) 0 []
        (by intro i hi; cases hi) q hq)
  have hW : SupportedQuaternionBlocks (1+1) polyOne := supported_one _
  have h1 := character_insertion_nonnegative (blocks := 1) (slot := 0)
    (by decide) hW hbase hp 1
  have h2 := character_insertion_nonnegative (blocks := 1) (slot := 0)
    (by decide) hW hbase hp 2
  have hs : (0 : Q') ≤
      cOne * insertion 1 polyOne p (characterPolynomial scalar 1) +
      cTwo * insertion 1 polyOne p (characterPolynomial scalar 2) :=
    Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide) h1)
      (Q'.mul_nonneg _ _ (by decide) h2)
  have he : insertion 1 polyOne p R ≈
      cOne * insertion 1 polyOne p (characterPolynomial scalar 1) +
      cTwo * insertion 1 polyOne p (characterPolynomial scalar 2) :=
    Q'.eqv_trans _ _ _ (insertion_coeff 1 polyOne p residual_character_pin)
      (Q'.eqv_trans _ _ _ (insertion_add 1 polyOne p _ _)
        (Q'.add_eqv_congr'
          (insertion_smul 1 polyOne p _ cOne)
          (insertion_smul 1 polyOne p _ cTwo)))
  exact Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv he)

/-- Unit endpoint source and first-coordinate probe. -/
def a : RatPoly := polyOne
def f : RatPoly := (PolyQuaternion.coordinateVariable 0).scalar

theorem f_supported : SupportedQuaternionBlocks 1 f :=
  (QuaternionHaarUnitScalarSquare.Supported.coordinate
    (blocks := 1) (block := 0) (by decide)).scalar

/-- Bilinear residual pairing on the original two-head Haar carrier. -/
def residualPair (p q : RatPoly) : Q' :=
  quaternionHaar 2 (polyMul (polyMul a (polyMul p (liftBoundary 1 q))) R)

def ownMean : Q' := quaternionHaar 2 (polyMul K f)
def ownSecond : Q' := quaternionHaar 2 (polyMul K (polyMul f f))
def residualMass : Q' := residualPair a a
def mixed : Q' := residualPair a (polyMul a (polyMul f f))
def diagonal : Q' := residualPair (polyMul a f) (polyMul a f)
def energyRemainder : Q' := mixed + -diagonal

/-- The probe is centered in its own actual heat-weighted law. -/
theorem own_source_moments :
    quaternionHaar 2 K ≈ 1 ∧ ownMean ≈ 0 ∧
    ownSecond ≈ Q'.mkPos 1 4 (by decide) := by
  decide

/-- Residual row sum and mixed coordinate-square term both vanish, while the
diagonal PSD entry is strictly positive. -/
theorem residual_entries :
    residualMass ≈ 0 ∧ mixed ≈ 0 ∧
    diagonal ≈ Q'.mkPos 15 256 (by decide) := by
  decide

/-- PSD does not give the mixed-minus-diagonal energy a positive sign. -/
theorem energy_remainder_exact :
    energyRemainder ≈ -(Q'.mkPos 15 256 (by decide)) ∧
    energyRemainder < (0 : Q') := by
  decide

#print axioms K
#print axioms scalar
#print axioms R
#print axioms heat_kernel_pin
#print axioms scalar_pair_pin
#print axioms residual_character_pin
#print axioms heat_floor_certificate
#print axioms residual_quadratic_nonnegative
#print axioms a
#print axioms f
#print axioms f_supported
#print axioms residualPair
#print axioms ownMean
#print axioms ownSecond
#print axioms residualMass
#print axioms mixed
#print axioms diagonal
#print axioms energyRemainder
#print axioms own_source_moments
#print axioms residual_entries
#print axioms energy_remainder_exact

end AlignmentEnergy

end YMGap.Continuum.QuaternionHaarConditionalRegressionWitness
