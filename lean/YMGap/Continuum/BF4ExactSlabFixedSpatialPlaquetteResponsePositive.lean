/-
# A detecting polynomial and positive ORIGINAL finite plaquette response

For h=chi_plaquette-m, the explicit polynomial b=w^(-12)*chi_plaquette-m
satisfies P(b)=h under every supported Haar test. Thus the original detector
with its ENTIRE interacting endpoint is H[V*T^n1*h^2]. Actual spatial and
terminal-message floor certificates, and H[h^2]>=1, make it strictly positive.
The preceding computed responseFloor is therefore positive for this test.

The theorem concerns the literal original finite one-step window. Its lower
bound retains cutoff, terminal depth, width and nome dependence. No uniform
positive limit, completed response floor, physical mass or continuum survival
is concluded from finite strict positivity alone.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
import YMGap.Continuum.SU2QuaternionProductHeatConstant
import YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow
  (messageFloor messageFloor_positive messageFloorCertificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff headFloor headFloor_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage weightedMass

private theorem power_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ k, (0 : Q') < qpow w k
  | 0 => by change (0 : Q') < 1; decide
  | k+1 => Q'.mul_pos (power_positive hw k) hw

def source (width : Nat) (face : Z4Plaq) (m : Q') : RatPoly :=
  shifted (characterPolynomial (plaquette width face).scalar 1) m

def dualTest {w : Q'} (hw0 : (0 : Q') < w) (width : Nat) (face : Z4Plaq) (m : Q') : RatPoly :=
  polyAdd (polySmul (Q'.recipPos (qpow w 12) (power_positive hw0 12))
    (characterPolynomial (plaquette width face).scalar 1)) (polySmul (-m) polyOne)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem source_supported (width : Nat) (face : Z4Plaq) (m : Q') :
    SupportedQuaternionBlocks (N width) (source width face m) :=
  shifted_supported (plaquette_supported width face) m

theorem dualTest_supported {w : Q'} (hw0 : (0 : Q') < w) (width : Nat) (face : Z4Plaq) (m : Q') :
    SupportedQuaternionBlocks (N width) (dualTest hw0 width face m) :=
  supported_add (support_smul (plaquette_supported width face) _)
    (support_smul (supported_one _) (-m))

/-- An actual finite auxiliary preimage. No inversion of V or terminal message. -/
theorem dualTest_preimage {w : Q'} (hw0 : (0 : Q') < w)
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : 1 ≤ K) (m : Q') :
    SupportedHaarEqv (N width) (productMap (N width) w K (activeBlocks width)
      (dualTest hw0 width face m)) (source width face m) := by
  let f := characterPolynomial (plaquette width face).scalar 1
  let r := Q'.recipPos (qpow w 12) (power_positive hw0 12)
  have hr : r*qpow w 12 ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  have he := (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
    (productMap_smul (N width) w K (activeBlocks width) r f))).trans
    ((plaquette_kinetic_eigen width face hf hactive w K hK).smul r)
  have hc : RatPolyCoeffEqv (polySmul r (polySmul (qpow w 12) f)) (polySmul 1 f) :=
    (RatPolyCoeffEqv.smul_assoc _ _ _).trans (RatPolyCoeffEqv.smul_coefficient hr f)
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
    (productMap_add (N width) w K (activeBlocks width) (polySmul r f) (polySmul (-m) polyOne)))).trans
    ((he.trans (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hc))).add
      (productMap_cap (N width) w K (activeBlocks width) (activeBlocks_nodup width)
        (activeBlocks_lt width) (-m)))

/-- The full original dependent endpoint remains in the detector. -/
theorem detector_pin {w : Q'} (hw0 : (0 : Q') < w)
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : 1 ≤ K) (n : Nat) (m : Q') :
    detector w K width n (source width face m) (dualTest hw0 width face m) ≈
      weightedMass w K width (polyMul (terminalMessage w K width n)
        (polyMul (source width face m) (source width face m))) := by
  unfold weightedMass
  exact Q'.eqv_trans _ _ _
    ((dualTest_preimage hw0 width face hf hactive K hK m)
      (weightedSource w K width n (source width face m))
      (weightedSource_supported w K width n (source_supported width face m)))
    (haar_of_coeff ((RatPolyCoeffEqv.mul_assoc _ _ _).trans
      ((RatPolyCoeffEqv.mul_assoc _ _ _).mul_left _)))

/-- Explicit positive finite detector floor, retaining the actual terminal mass. -/
theorem detector_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) (m : Q') :
    messageFloor w K width n * (headFloor w)^(spatialFaces width).length ≤
      detector w K width n (source width face m) (dualTest hw0 width face m) := by
  let h := source width face m
  let c := (headFloor w)^(spatialFaces width).length
  have hh := source_supported width face m
  have hc : (0 : Q') ≤ c := Q'.le_of_lt (HKPos.pow_pos (headFloor_positive hw0 hw1) _)
  have hbare := shifted_square_floor width face hf m
  have hspatial : c ≤ weightedMass w K width (polyMul h h) := by
    unfold weightedMass
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv c))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ c hbare hc)
        (raw_square_floor (spatialFloorCertificate hw0 hw1 K width hK) hh))
  have hm := Q'.le_of_lt (messageFloor_positive hw0 hw1 K width hK n)
  have hterm := weightedMass_product_floor hw0 hw1 K width hK
    (Certificate.square h hh) (messageFloorCertificate hw0 hw1 K width hK n)
  have hpin := Q'.eqv_trans _ _ _ (detector_pin hw0 width face hf hactive K hK1 n m)
    (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (messageFloor w K width n) hspatial hm)
    (Q'.le_trans' _ _ _ hterm (Q'.ge_of_eqv hpin))

theorem detector_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) (m : Q') :
    (0 : Q') < detector w K width n (source width face m) (dualTest hw0 width face m) :=
  Q'.pos_of_lt_of_le
    (Q'.mul_pos (messageFloor_positive hw0 hw1 K width hK n)
      (HKPos.pow_pos (headFloor_positive hw0 hw1) _))
    (detector_floor hw0 hw1 width face hf hactive K hK hK1 n m)

/-- The preceding computable lower bound now has an actual detecting test. -/
theorem responseFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) (m : Q') :
    (0 : Q') < responseFloor hw0 hw1 K width hK n (source width face m)
      (dualTest hw0 width face m) (dualTest_supported hw0 width face m) := by
  have hd := detector_positive hw0 hw1 width face hf hactive K hK hK1 n m
  exact Q'.mul_pos (Q'.mul_pos (Q'.mul_pos hd hd) (Q'.recipPos_pos _ _)) (Q'.recipPos_pos _ _)

/-- Literal original finite one-step response; strict positivity is NOT a
uniform positive lower bound after any limit. -/
theorem window_response_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) (m : Q') :
    (0 : Q') < windowRatio hw0 hw1 K width hK n 1 n
      (polyMul (source width face m) (liftBoundary (N width) (source width face m))) :=
  Q'.pos_of_lt_of_le (responseFloor_positive hw0 hw1 width face hf hactive K hK hK1 n m)
    (responseFloor_le_window hw0 hw1 K width hK n
      (source_supported width face m) (dualTest_supported hw0 width face m))

/-- Choose the already computed ORIGINAL odd marginal mean, not a Haar mean. -/
theorem centered_window_response_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) :
    let m := middleRatio hw0 hw1 K width hK (n+1) n
      (characterPolynomial (plaquette width face).scalar 1)
    (0 : Q') < windowRatio hw0 hw1 K width hK n 1 n
      (polyMul (source width face m) (liftBoundary (N width) (source width face m))) :=
  window_response_positive hw0 hw1 width face hf hactive K hK hK1 n _

/-- Every fixed base face has positive centered original finite response at
each strictly larger width. The floor still need not survive any limit. -/
theorem padded_centered_window_response_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) :
    let m := middleRatio hw0 hw1 K width hK (n+1) n
      (characterPolynomial (plaquette width face).scalar 1)
    (0 : Q') < windowRatio hw0 hw1 K width hK n 1 n
      (polyMul (source width face m) (liftBoundary (N width) (source width face m))) :=
  centered_window_response_positive hw0 hw1 width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf) K hK hK1 n

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.dualTest
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.source_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.dualTest_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.dualTest_preimage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.detector_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.detector_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.detector_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.responseFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.window_response_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.centered_window_response_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive.padded_centered_window_response_positive
