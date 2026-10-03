/-
# Exact terminal-source testing against the ORIGINAL interacting transfer

The first cube face has the exact bare kinetic multiplier w^12 for K>=1.
Move this test through the original kinetic map while retaining the entire
original spatial weight. This works for every supported source, not only
cube-local or fringe-independent sources. In particular the actual
g_n*(F-c_n) source remains inside the SAME original weighted functional.

No positive overlap, terminal mean bound, gain sign, completed response or
changing-family survival is asserted by this identity.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTest

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer (kineticMap_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (bentObservable bentObservable_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (centeredMessage)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks transferStep spatialWeight weightedMass terminalMessage

private theorem firstFace_supported : SupportedQuaternionBlocks N firstFaceTrace :=
  character_supported (plaquette_supported 2 N (Nat.le_refl _) ((0,0,0,0),.p01)).scalar 1

private theorem firstFace_eigen (w : Q') (K : Nat) (hK : 1 ≤ K) :
    SupportedHaarEqv N (productMap N w K (activeBlocks 2) firstFaceTrace)
      (polySmul (qpow w 12) firstFaceTrace) := by
  have hbase := (spatialFaces_mem_iff 1 ((0,0,0,0),.p01)).mpr (by decide)
  have hface := (spatialFaces_mem_iff 2 ((0,0,0,0),.p01)).mpr (by decide)
  exact plaquette_kinetic_eigen 2 ((0,0,0,0),.p01) hface
    (plaquette_active_after_padding (by decide : 1 < 2) _ hbase) w K hK

/-- The full original action remains inside the weighted source. There is
NO locality hypothesis on f and no interaction eigenpin for f. -/
theorem firstFace_transfer_test (w : Q') (K : Nat) (hK : 1 ≤ K) {f : RatPoly}
    (hf : SupportedQuaternionBlocks N f) :
    quaternionHaar N (polyMul firstFaceTrace (transferStep w K 2 f)) ≈
      qpow w 12 * weightedMass w K 2 (polyMul firstFaceTrace f) := by
  let V := spatialWeight w K 2
  have hs : SupportedQuaternionBlocks N (polyMul V f) :=
    supported_polyMul (spatialWeight_supported w K 2) hf
  have h0 : quaternionHaar N (polyMul firstFaceTrace (transferStep w K 2 f)) ≈
      quaternionHaar N (polyMul (polyMul V f)
        (productMap N w K (activeBlocks 2) firstFaceTrace)) := by
    rw [transferStep_eq_productMap]
    exact kineticMap_symmetric w K 2 hs firstFace_supported
  have h1 := firstFace_eigen w K hK (polyMul V f) hs
  have h2 := quaternionHaar_polyMul_smul_right N (qpow w 12) (polyMul V f) firstFaceTrace
  have he : RatPolyCoeffEqv (polyMul (polyMul V f) firstFaceTrace)
      (polyMul V (polyMul firstFaceTrace f)) :=
    (RatPolyCoeffEqv.mul_assoc V f firstFaceTrace).trans
      ((RatPolyCoeffEqv.refl V).mul (RatPolyCoeffEqv.mul_comm f firstFaceTrace))
  unfold weightedMass
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2 (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff he))))

/-- At every actual terminal depth, the literal centered-message test has
the SAME full V*g_n source and arbitrary supplied center c. -/
theorem terminal_centered_test (w : Q') (K : Nat) (hK : 1 ≤ K) (n : Nat) (c : Q') :
    quaternionHaar N (polyMul firstFaceTrace
      (centeredMessage w K 2 n bentObservable c)) ≈
      qpow w 12 * weightedMass w K 2
        (polyMul firstFaceTrace
          (polyMul (terminalMessage w K 2 n) (shifted bentObservable c))) := by
  unfold centeredMessage
  exact firstFace_transfer_test w K hK
    (supported_polyMul (terminalMessage_supported w K 2 n)
      (shifted_supported bentObservable_supported c))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTest

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTest.firstFace_transfer_test
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTest.terminal_centered_test
