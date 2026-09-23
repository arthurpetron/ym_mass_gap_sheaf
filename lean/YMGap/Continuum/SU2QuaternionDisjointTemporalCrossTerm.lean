/-
# A nonzero temporal cross term on two disjoint quaternion blocks

This finite example records that disjoint block support does not make the
mixed term of the endpoint-corrected product-heat energy vanish.  It uses the
actual two-block `productMap`, source `1 + (1/2) x*y` with a certified
Haar-order half floor, and positive cutoff-one, nome-one-half heat kernels.

This source is a diagnostic polynomial, not the physical BF4 endpoint source
`V*g`.  The result therefore neither obstructs a coefficient-square upper
bound nor supplies any physical or continuum estimate.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
import YMGap.Continuum.QuaternionHaarSharpCharacterInterval

namespace YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval

local infix:50 " ≈ " => Q'.eqv

def nome : Q' := Q'.mkPos 1 2 (by decide)
def x : RatPoly := polyVar 0
def y : RatPoly := polyVar 4
def source : RatPoly :=
  polyAdd polyOne (polySmul (Q'.mkPos 1 2 (by decide)) (polyMul x y))

def P (f : RatPoly) : RatPoly := productMap 2 nome 1 [0, 1] f

/-- Both terms of the original endpoint-corrected form, kept together. -/
def correctedEnergy (f : RatPoly) : Q' :=
  quaternionHaar 2 (polyMul (polyMul source (polyMul f f)) (P source)) +
    -(quaternionHaar 2 (polyMul (polyMul source f) (P (polyMul source f))))

/-- The mixed polarization of the complete corrected energy:
`H[(a*x*y) P(a)] - H[(a*x) P(a*y)]`. -/
def mixedCorrectedEnergy : Q' :=
  quaternionHaar 2 (polyMul (polyMul source (polyMul x y)) (P source)) +
    -(quaternionHaar 2
      (polyMul (polyMul source x) (P (polyMul source y))))

/-- The source-dependent one-time marginal density for this example. -/
def marginal : RatPoly := polyMul source (P source)

def marginalMass : Q' := quaternionHaar 2 marginal

theorem x_supported : SupportedQuaternionBlocks 2 x := by
  intro term hterm
  simp only [x, polyVar, List.mem_singleton] at hterm
  subst term
  decide

theorem y_supported : SupportedQuaternionBlocks 2 y := by
  intro term hterm
  simp only [y, polyVar, List.mem_singleton] at hterm
  subst term
  decide

private def xySquare : SquareBound 2 (polyMul x y) 1 :=
  ((SquareBound.scalar (Supported.coordinate (by decide : 0 < 2))
    (haarNorm_coordinate (by decide : 0 < 2))).mul
    (SquareBound.scalar (Supported.coordinate (by decide : 1 < 2))
      (haarNorm_coordinate (by decide : 1 < 2)))).changeCap (by decide)

theorem source_supported : SupportedQuaternionBlocks 2 source :=
  supported_add (supported_one 2) ((unitSquareInterval xySquare).smul nome (by decide)).support

/-- A witnessing square certificate for a >= 1/2 on the original Haar
carrier, valid under arbitrary supported square insertions. -/
def sourceFloor_certificate : Certificate 2 (polyAdd source (polyNeg (cap nome))) :=
  .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.smul nome (by decide) (unitSquareInterval xySquare).lower)

def source_certificate : Certificate 2 source :=
  .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.add sourceFloor_certificate (.constant 2 nome (by decide)))

private def relativeSquare (i j : Nat) (hi : i < 4) (hj : j < 4) :
    SquareBound 4 (scalarAt i j) 1 :=
  SquareBound.scalar ((Supported.coordinate hi).mul (Supported.coordinate hj).conj)
    (haarNorm_mul (haarNorm_coordinate hi)
      ((RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _)).trans (haarNorm_coordinate hj)))

/-- Each actual cutoff-one heat factor has its own positive half floor.
No eventual-cutoff positivity premise is assumed for this finite example. -/
def firstHeatFloor_certificate :
    Certificate 4 (polyAdd (heatAt 0 2 nome 1) (polyNeg (cap nome))) :=
  .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.smul nome (by decide) (unitSquareInterval (relativeSquare 0 2 (by decide) (by decide))).lower)

def secondHeatFloor_certificate :
    Certificate 4 (polyAdd (heatAt 1 3 nome 1) (polyNeg (cap nome))) :=
  .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.smul nome (by decide) (unitSquareInterval (relativeSquare 1 3 (by decide) (by decide))).lower)

def kernel_certificate : Certificate 4 (productHeat 2 nome 1 [0, 1]) := by
  let h0 : Certificate 4 (heatAt 0 2 nome 1) :=
    .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
      (.add firstHeatFloor_certificate (.constant 4 nome (by decide)))
  let h1 : Certificate 4 (heatAt 1 3 nome 1) :=
    .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
      (.add secondHeatFloor_certificate (.constant 4 nome (by decide)))
  exact .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide)) (h0.mul h1)

/-- The entire two-endpoint density is certified positive, with the SAME
source on both sides of the SAME original product heat. -/
def edge_certificate : Certificate 4 (edgeWeight 2 nome 1 [0, 1] source) :=
  (kernel_certificate.mul (certificate_extend 2 source_supported source_certificate)).mul
    (lift_certificate 2 source_certificate)

/-- Here P(a) is an explicit convex combination of a and the constant one.
This is a checked identity for the actual map, not a positivity assumption. -/
def propagatedSource_certificate : Certificate 2 (P source) := by
  let c := Q'.mkPos 1 64 (by decide)
  let d := Q'.mkPos 63 64 (by decide)
  let C : Certificate 2 (polyAdd (polySmul c source) (cap d)) :=
    .add (.smul c (by decide) source_certificate) (.constant 2 d (by decide))
  exact .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide)) C

def marginal_certificate : Certificate 2 marginal :=
  source_certificate.mul propagatedSource_certificate

/-- `x` is independent of the block carrying `y`. -/
theorem x_independent_second : QuaternionBlockIndependent 1 x := by
  simpa [x] using
    (quaternionBlockIndependent_polyVar_of_distinctBlock
      (source := 0) (target := 1) (component := 0) (by decide) (by decide))

/-- `y` is independent of the block carrying `x`. -/
theorem y_independent_first : QuaternionBlockIndependent 0 y := by
  simpa [y] using
    (quaternionBlockIndependent_polyVar_of_distinctBlock
      (source := 1) (target := 0) (component := 0) (by decide) (by decide))

/-- The actual source-dependent marginal has positive, explicitly computed
mass. -/
theorem marginalMass_value :
    marginalMass ≈ Q'.mkPos 4097 4096 (by decide) := by decide

/-- The first disjoint coordinate is already centered in the same marginal
used by the corrected temporal form. -/
theorem marginal_x_zero :
    quaternionHaar 2 (polyMul marginal x) ≈ 0 := by decide

/-- The second disjoint coordinate is also centered in that marginal. -/
theorem marginal_y_zero :
    quaternionHaar 2 (polyMul marginal y) ≈ 0 := by decide

/-- Exact nonzero mixed term.  Here the fundamental transmission factor is
`(1/2)^3 = 1/8`, so the value is
`(1/2) * (1 - 1/8)^2 * (1/16) = 49/2048`. -/
theorem mixedCorrectedEnergy_value :
    mixedCorrectedEnergy ≈ Q'.mkPos 49 2048 (by decide) := by decide

theorem mixedCorrectedEnergy_ne_zero :
    ¬ mixedCorrectedEnergy ≈ 0 := by
  intro hzero
  have hbad : Q'.mkPos 49 2048 (by decide) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm mixedCorrectedEnergy_value) hzero
  exact (by decide : ¬ (Q'.mkPos 49 2048 (by decide) ≈ (0 : Q'))) hbad

/-- The actual mixed jump integral, not a separately assigned matrix entry. -/
def edgeMixedEnergy : Q' :=
  weightedPair 4 (edgeWeight 2 nome 1 [0, 1] source)
    (SU2QuaternionWeightedProductDualEnergy.jump 2 x)
    (SU2QuaternionWeightedProductDualEnergy.jump 2 y)

/-- Consume the arbitrary-source original mixed-form identity. -/
theorem edgeMixedEnergy_pin : edgeMixedEnergy ≈ 2 * mixedCorrectedEnergy := by
  have hp := SU2QuaternionWeightedProductDualEnergy.full_jump_pairing 2 nome 1 [0, 1]
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)
    source_supported x_supported y_supported
  have hm : SU2QuaternionWeightedProductDualEnergy.marginalPair 2 nome 1 [0, 1] source x y ≈
      quaternionHaar 2 (polyMul (polyMul source (polyMul x y)) (P source)) :=
    haar_of_coeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
  exact Q'.eqv_trans _ _ _ hp (Q'.mul_eqv_congr_left 2 _ _
    (Q'.add_eqv_congr' hm (Q'.eqv_refl _)))

theorem edgeMixedEnergy_value : edgeMixedEnergy ≈ Q'.mkPos 49 1024 (by decide) :=
  Q'.eqv_trans _ _ _ edgeMixedEnergy_pin
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ mixedCorrectedEnergy_value) (by decide))

/-- The disjoint, already centered observables do not have additive energy. -/
theorem energy_nonadditivity_value :
    correctedEnergy (polyAdd x y) + -(correctedEnergy x + correctedEnergy y) ≈
      Q'.mkPos 49 1024 (by decide) := by decide

/-- Explicit inverse of the SAME positive partition, not a new law. -/
def normalizer : Q' := Q'.mkPos 4096 4097 (by decide)

theorem normalizer_pin : marginalMass * normalizer ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ normalizer marginalMass_value) (by decide)

theorem normalizedMixed_value :
    mixedCorrectedEnergy * normalizer ≈ Q'.mkPos 98 4097 (by decide) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ normalizer mixedCorrectedEnergy_value) (by decide)

end YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm

#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.x_supported
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.y_supported
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.source_supported
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.sourceFloor_certificate
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.source_certificate
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.firstHeatFloor_certificate
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.secondHeatFloor_certificate
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.kernel_certificate
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.edge_certificate
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.propagatedSource_certificate
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.marginal_certificate
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.x_independent_second
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.y_independent_first
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.marginalMass_value
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.marginal_x_zero
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.marginal_y_zero
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.mixedCorrectedEnergy_value
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.mixedCorrectedEnergy_ne_zero
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.edgeMixedEnergy_pin
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.edgeMixedEnergy_value
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.energy_nonadditivity_value
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.normalizer_pin
#print axioms YMGap.Continuum.SU2QuaternionDisjointTemporalCrossTerm.normalizedMixed_value
