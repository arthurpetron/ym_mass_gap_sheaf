/-
# An actual original-action marginal is not a constant heat-only marginal

At width two and cutoff one the fundamental face test of the actual original
T1 is w^12*(alpha+alpha^5/16), alpha=2*w^3, strictly positive for w>0.
The same test of every constant is zero. Thus T1 is not even supported-Haar
equivalent to any constant, whereas the original FREE kinetic map sends one
to one in exactly that tested sense at EVERY width, nome and cutoff.

The full spatial action is retained through the existing original transfer
and exact fringe integration. No raw polynomial expansion is performed.
This rules out dropping the spatial action in this finite marginal. It does
NOT rule out every coarse kinetic-plus-spatial action, identify the ambient
gluedMiddle marginal with T1, or assert cutoff-one positivity, a normalized
continuum comparison, a transfer gap or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap_pairing)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (kineticWeight_upper_marginal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticContraction (kineticMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer
  (tested_vacuum_transfer_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeVacuumActionMoment
  (tested_vacuum_action_channel)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar
  (plaquette_supported plaquette_mean_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces_mem_iff)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser (qpow qpow_succ)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks

private theorem positive_power {w : Q'} (hw : (0 : Q') < w) :
    ∀ n, (0 : Q') < qpow w n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos (positive_power hw n) hw

private theorem firstFace_supported : SupportedQuaternionBlocks (N 2) firstFaceTrace :=
  plaquette_supported 2 ((0,0,0,0),.p01)

private theorem firstFace_mean_zero : quaternionHaar (N 2) firstFaceTrace ≈ 0 :=
  plaquette_mean_zero 2 ((0,0,0,0),.p01)
    ((spatialFaces_mem_iff 2 ((0,0,0,0),.p01)).mpr (by decide))

/-- The original free kinetic marginal is exactly one as a tested functional.
No positive cutoff threshold or nome restriction is needed. -/
theorem kineticMap_one_haar (w : Q') (K width : Nat) :
    SupportedHaarEqv (N width) (kineticMap w K width polyOne) polyOne := by
  intro p hp
  have h0 := haar_of_coeff (blocks := N width)
    (RatPolyCoeffEqv.mul_comm p (kineticMap w K width polyOne))
  have h1 := Q'.eqv_symm
    (kernelMap_pairing (N width) (kineticWeight w K width) polyOne p)
  unfold QuaternionHaarWeightedCauchySchwarz.weightedPair at h1
  have h2 := haar_of_coeff (blocks := N width+N width)
    (((RatPolyCoeffEqv.one_mul (liftBoundary (N width) p)).mul_right
      (kineticWeight w K width)).trans
      (RatPolyCoeffEqv.mul_comm (liftBoundary (N width) p) (kineticWeight w K width)))
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2 (Q'.eqv_trans _ _ _
      (kineticWeight_upper_marginal w K width p hp)
      (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one p))))))

/-- Exact actual first-message test, including its kinetic attenuation. -/
theorem tested_original_one_exact (w : Q') :
    quaternionHaar (N 2) (polyMul firstFaceTrace (transferStep w 1 2 polyOne)) ≈
      qpow w 12 * (coeffW w 1 + qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide)) :=
  Q'.eqv_trans _ _ _ (tested_vacuum_transfer_pin w 1 (by decide))
    (Q'.mul_eqv_congr_left _ _ _ (tested_vacuum_action_channel w))

/-- A strict original-action witness, not a claim that the cutoff action is
positive at all positive w. -/
theorem tested_original_one_positive {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < quaternionHaar (N 2)
      (polyMul firstFaceTrace (transferStep w 1 2 polyOne)) := by
  have ha : (0 : Q') < coeffW w 1 :=
    Q'.mul_pos (by decide) (positive_power hw 3)
  have hs : (0 : Q') < coeffW w 1 +
      qpow (coeffW w 1) 5 * Q'.mkPos 1 16 (by decide) :=
    Q'.pos_of_lt_of_le ha (Q'.add_le_self_of_nonneg _ _
      (Q'.le_of_lt (Q'.mul_pos (positive_power ha 5) (by decide))))
  exact Q'.pos_of_lt_of_le (Q'.mul_pos (positive_power hw 12) hs)
    (Q'.ge_of_eqv (tested_original_one_exact w))

/-- Every possible scalar multiple of one fails the actual face test. -/
theorem original_one_not_constant {w : Q'} (hw : (0 : Q') < w) (c : Q') :
    ¬ SupportedHaarEqv (N 2) (transferStep w 1 2 polyOne) (polySmul c polyOne) := by
  intro h
  have hz : quaternionHaar (N 2) (polyMul firstFaceTrace (polySmul c polyOne)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (N 2) c firstFaceTrace polyOne)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one firstFaceTrace))
          firstFace_mean_zero)) (Q'.mul_zero_eqv c))
  have hzero := Q'.eqv_trans _ _ _ (h firstFaceTrace firstFace_supported) hz
  exact (Int.lt_irrefl _) (Q'.lt_of_le_of_lt (Q'.le_of_eqv hzero)
    (tested_original_one_positive hw))

/-- No change of the free heat nome or cutoff repairs the missing spatial
action in this marginal. The same physical face detects every such change. -/
theorem original_one_not_free {w : Q'} (hw : (0 : Q') < w) (wC : Q') (KC : Nat) :
    ¬ SupportedHaarEqv (N 2) (transferStep w 1 2 polyOne) (kineticMap wC KC 2 polyOne) := by
  intro h
  have hc := h.trans (kineticMap_one_haar wC KC 2)
  have he : RatPolyCoeffEqv polyOne (polySmul 1 polyOne) :=
    (RatPolyCoeffEqv.one_smul polyOne).symm
  have hh : SupportedHaarEqv (N 2) (transferStep w 1 2 polyOne) (polySmul 1 polyOne) :=
    fun p hp => Q'.eqv_trans _ _ _ (hc p hp) (haar_of_coeff (he.mul_left p))
  exact original_one_not_constant hw 1 hh

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction.kineticMap_one_haar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction.tested_original_one_exact
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction.tested_original_one_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction.original_one_not_constant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction.original_one_not_free
