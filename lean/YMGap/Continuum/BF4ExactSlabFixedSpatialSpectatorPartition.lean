/-
# Original odd partition bounded by the same spectator kinetic quadratic

The odd mass is the original finite Wilson transfer quadratic.  The local
endpoint certificate compares its complete endpoint with the spectator that
retains every exterior factor.  Positive order for the actual product heat
then bounds the odd mass by the spectator kinetic quadratic.  This is a
fixed-width, finite-cutoff statement, not a spatial-limit response bound.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
import YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorPartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
  (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
  (original_quadratic_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalSpectator
  (spectator spectator_supported spectator_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
  (localUpper localUpper_positive endpoint_localUpperCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
  (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm (kineticPair)
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder
  (kineticPair_quadratic_cap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound (edgesOf_length)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- The successor odd mass is precisely the original kinetic quadratic of
the complete endpoint, before any local comparison. -/
theorem oddMass_endpoint_kinetic_pin (w : Q') (K width n : Nat) :
    oddMass w K width (n+1) ≈
      kineticPair (N width) w K (activeBlocks width)
        (polyMul (spatialWeight w K width) (terminalMessage w K width (n+1)))
        (polyMul (spatialWeight w K width) (terminalMessage w K width (n+1))) := by
  change weightedMass w K width
    (polyMul (terminalMessage w K width ((n+1)+1))
      (terminalMessage w K width (n+1))) ≈ _
  rw [← terminalMessage_next w K width (n+1)]
  exact Q'.eqv_trans _ _ _
    (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _))
    (original_quadratic_pin w K width (terminalMessage w K width (n+1)))

/-- The actual finite odd partition is controlled by the same exterior
spectator quadratic, with a four-link constant independent of width/depth. -/
theorem oddMass_spectator_cap {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n : Nat) (face : Z4Plaq) :
    oddMass w K width (n+1) ≤
      (localUpper w 4 * localUpper w 4) *
        kineticPair (N width) w K (activeBlocks width)
          (spectator w K width n (edgesOf face))
          (spectator w K width n (edgesOf face)) := by
  have hsize : (edgesOf face).length ≤ 4 := by
    rw [edgesOf_length]
    exact Nat.le_refl _
  have hcap := kineticPair_quadratic_cap (N width) hw0 hw1 K hK
    (activeBlocks width) (activeBlocks_lt width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width (n+1)))
    (spectator_supported w K width n (edgesOf face))
    ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK (n+1)))
    (spectator_certificate hw0 hw1 K width hK n (edgesOf face))
    (localUpper w 4) (Q'.le_of_lt (localUpper_positive hw0 hw1 4))
    (endpoint_localUpperCertificate hw0 hw1 K width hK n (edgesOf face) 4 hsize)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (oddMass_endpoint_kinetic_pin w K width n)) hcap

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorPartition

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorPartition.oddMass_endpoint_kinetic_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpectatorPartition.oddMass_spectator_cap
