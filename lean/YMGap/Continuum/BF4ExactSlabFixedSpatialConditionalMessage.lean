/-
# One-coordinate control of the ACTUAL finite terminal message

Remove exactly one active kinetic factor from the final step of u_(n+1).
The resulting explicit polynomial r_i is independent of output coordinate i
and equals P_i(u_(n+1)) against every supported Haar insertion. The same
full remaining kernel gives certificates h*r_i <= u_(n+1) <= U*r_i, where
h=headFloor(w) and U=prefixCap(w). Neither constant has a width/depth power.

This is division-free conditional-message normalization control. It does
not bound V*u_(n+1) by an independent reference, supply a reciprocal, make
the terminal weight local, or control signed mixed energy defects. Those
defects, not an assumed orthogonal decomposition, remain the global gap join.
-/

import YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff headFloor)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra (project_congr)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm mem_of_mem_erase not_mem_erase)
open YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] kineticWeight spatialWeight baseLinks

/-- The computed final step with only the selected kinetic factor removed.
The original spatial weight and entire previous terminal message remain. -/
def conditionalMessage (w : Q') (K width n i : Nat) : RatPoly :=
  productMap (N width) w K (eraseIndex i (activeBlocks width))
    (polyMul (spatialWeight w K width) (terminalMessage w K width n))

private theorem remaining_lt (width i : Nat) (j : Nat)
    (hj : j ∈ eraseIndex i (activeBlocks width)) : j < N width :=
  activeBlocks_lt width j (mem_of_mem_erase i hj)

theorem conditionalMessage_supported (w : Q') (K width n i : Nat) :
    SupportedQuaternionBlocks (N width) (conditionalMessage w K width n i) :=
  productMap_supported (N width) w K _ (remaining_lt width i)
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))

theorem conditionalMessage_independent (w : Q') (K width n i : Nat)
    (hi : i ∈ activeBlocks width) :
    QuaternionBlockIndependent i (conditionalMessage w K width n i) :=
  productMap_independent_of_not_mem (N width) w K _ (remaining_lt width i) i
    (activeBlocks_lt width i hi) (not_mem_erase i (activeBlocks_nodup width)) _
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))

private theorem terminal_cons_pin (w : Q') (K width n i : Nat)
    (hi : i ∈ activeBlocks width) :
    RatPolyCoeffEqv (terminalMessage w K width (n+1))
      (productMap (N width) w K (i::eraseIndex i (activeBlocks width))
        (polyMul (spatialWeight w K width) (terminalMessage w K width n))) := by
  rw [← terminalMessage_next]
  unfold transferStep step
  rw [kineticWeight_eq_indexedProduct]
  exact partialHaarHeads_congr (N width)
    ((polynomialProduct_perm _ (select_perm i hi)).mul_right _)

/-- Literal conditional normalization at the supported-Haar level; no
coefficient identity for the sphere heat normalization is asserted. -/
theorem conditionalMessage_pin (w : Q') (K width n i : Nat)
    (hi : i ∈ activeBlocks width) :
    SupportedHaarEqv (N width) (project i (terminalMessage w K width (n+1)))
      (conditionalMessage w K width n i) :=
  (SupportedHaarEqv.of_carrier
    (RatPolyCoeffEqv.haarCarrier (project_congr i (terminal_cons_pin w K width n i hi)))).trans
    (productMap_conditional_pin (N width) w K i _ (activeBlocks_lt width i hi)
      (not_mem_erase i (activeBlocks_nodup width)) (remaining_lt width i) _
      (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)))

/-- One-factor lower comparison for the actual message at every depth.
This is a certificate in the original polynomial cone, not an assumed order. -/
def conditionalMessage_lowerCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) (hi : i ∈ activeBlocks width) :
    Certificate (N width)
      (polyAdd (terminalMessage w K width (n+1))
        (polyNeg (polySmul (headFloor w) (conditionalMessage w K width n i)))) :=
  Certificate.ofCoeff ((terminal_cons_pin w K width n i hi).add (.refl _))
    (productMap_floorCertificate (N width) hw0 hw1 K hK i _
      (activeBlocks_lt width i hi) (remaining_lt width i)
      (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))
      ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
        (terminalMessage_certificate hw0 hw1 K width hK n)))

/-- Matching one-factor upper comparison, with the SAME retained message. -/
def conditionalMessage_capCertificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) (hi : i ∈ activeBlocks width) :
    Certificate (N width)
      (polyAdd (polySmul (prefixCap w) (conditionalMessage w K width n i))
        (polyNeg (terminalMessage w K width (n+1)))) :=
  Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add
    (RatPolyCoeffEqv.neg (terminal_cons_pin w K width n i hi)))
    (productMap_capCertificate (N width) hw0 hw1 K hK i _
      (activeBlocks_lt width i hi) (remaining_lt width i)
      (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))
      ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
        (terminalMessage_certificate hw0 hw1 K width hK n)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage.conditionalMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage.conditionalMessage_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage.conditionalMessage_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage.conditionalMessage_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage.conditionalMessage_lowerCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage.conditionalMessage_capCertificate
