/-
# Original finite terminal messages descend to the retained cube transfer

Iterate the six-face cube transfer from the unit input. The original
terminal message is related to this retained representative only under all
supported Haar insertions. The induction transports the prior relation
through the full original transfer using its kinetic symmetry and full
spatial weight, then applies the literal cube-source reduction to the
supported local representative. No raw terminal locality or product
factorization is assumed.

This is a finite source-identification bridge. It does not identify terminal
masses, variances, completed states, or a changing family.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer (kineticMap_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyOne)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productMap productMap_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)

local notation "N" => List.length (baseLinks 2)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight transferStep cubeWeight cubeTransfer

/-- Repeated application of the literal retained six-face transfer to `1`. -/
def cubeTerminal (K : Nat) : Nat → RatPoly
  | 0 => polyOne
  | n+1 => cubeTransfer smallNome K (cubeTerminal K n)

theorem cubeTerminal_supported (K n : Nat) :
    SupportedQuaternionBlocks N (cubeTerminal K n) := by
  induction n with
  | zero => exact supported_one N
  | succ n ih =>
      exact cubeTransfer_supported smallNome K ih

/-- Every iterated retained representative stays independent of each
non-retained original quaternion block. This is the locality needed by the
next application of `original_transfer_cube`; it is not asserted for the
raw original terminal polynomial. -/
theorem cubeTerminal_independent (K n i : Nat) (hi : i < N)
    (hnot : i ∉ cubeIndices) :
    QuaternionBlockIndependent i (cubeTerminal K n) := by
  cases n with
  | zero => exact quaternionBlockIndependent_polyOne i
  | succ n =>
      exact cubeTransfer_independent smallNome K i hi hnot
        (cubeTerminal_supported K n)

private theorem transfer_preserves_supportedHaarEqv (K : Nat) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks N f) (hg : SupportedQuaternionBlocks N g)
    (hfg : SupportedHaarEqv N f g) :
    SupportedHaarEqv N (transferStep smallNome K 2 f) (transferStep smallNome K 2 g) := by
  intro p hp
  let V := spatialWeight smallNome K 2
  let Pp := productMap N smallNome K (activeBlocks 2) p
  have hV : SupportedQuaternionBlocks N V := spatialWeight_supported smallNome K 2
  have hPp : SupportedQuaternionBlocks N Pp :=
    productMap_supported N smallNome K (activeBlocks 2) (activeBlocks_lt 2) hp
  have htest : SupportedQuaternionBlocks N (polyMul V Pp) := supported_polyMul hV hPp
  have hsourceF : SupportedQuaternionBlocks N (polyMul V f) := supported_polyMul hV hf
  have hsourceG : SupportedQuaternionBlocks N (polyMul V g) := supported_polyMul hV hg
  have hleft :
      (quaternionHaar N (polyMul p (transferStep smallNome K 2 f))).eqv
        (quaternionHaar N (polyMul (polyMul V f) Pp)) := by
    rw [transferStep_eq_productMap]
    exact kineticMap_symmetric smallNome K 2 hsourceF hp
  have hright :
      (quaternionHaar N (polyMul p (transferStep smallNome K 2 g))).eqv
        (quaternionHaar N (polyMul (polyMul V g) Pp)) := by
    rw [transferStep_eq_productMap]
    exact kineticMap_symmetric smallNome K 2 hsourceG hp
  have hpolyF : RatPolyCoeffEqv (polyMul (polyMul V f) Pp) (polyMul (polyMul V Pp) f) :=
    (RatPolyCoeffEqv.mul_assoc V f Pp).trans
      (((RatPolyCoeffEqv.mul_comm f Pp).mul_left V).trans
        (RatPolyCoeffEqv.mul_assoc V Pp f).symm)
  have hpolyG : RatPolyCoeffEqv (polyMul (polyMul V g) Pp) (polyMul (polyMul V Pp) g) :=
    (RatPolyCoeffEqv.mul_assoc V g Pp).trans
      (((RatPolyCoeffEqv.mul_comm g Pp).mul_left V).trans
        (RatPolyCoeffEqv.mul_assoc V Pp g).symm)
  have hmiddle := hfg (polyMul V Pp) htest
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ (haar_of_coeff hpolyF)
      (Q'.eqv_trans _ _ _ hmiddle
        (Q'.eqv_trans _ _ _ (haar_of_coeff hpolyG.symm) (Q'.eqv_symm hright))))

/-- The actual original terminal message and the iterated cube representative
agree under every supported Haar insertion, for every finite cutoff and lag.
At each induction step, the original raw message is passed through the full
transfer by its kinetic adjoint identity; only the reduced cube representative
is subjected to the cube-locality hypothesis. -/
theorem terminalMessage_cubeTerminal (K n : Nat) :
    SupportedHaarEqv N (terminalMessage smallNome K 2 n) (cubeTerminal K n) := by
  induction n with
  | zero =>
      change SupportedHaarEqv N polyOne polyOne
      exact SupportedHaarEqv.refl N polyOne
  | succ n ih =>
      have hraw := transfer_preserves_supportedHaarEqv K
        (terminalMessage_supported smallNome K 2 n)
        (cubeTerminal_supported K n) ih
      have hlocal : ∀ i, i < N → i ∉ cubeIndices →
          QuaternionBlockIndependent i (cubeTerminal K n) :=
        fun i hi hnot => cubeTerminal_independent K n i hi hnot
      have hcube := original_transfer_cube smallNome K
        (cubeTerminal_supported K n) hlocal
      rw [← terminalMessage_next smallNome K 2 n]
      change SupportedHaarEqv N
        (transferStep smallNome K 2 (terminalMessage smallNome K 2 n))
        (cubeTransfer smallNome K (cubeTerminal K n))
      exact hraw.trans hcube

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer.cubeTerminal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer.cubeTerminal_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer.cubeTerminal_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer.terminalMessage_cubeTerminal
