/-
# Conditional-channel regularity of the complete projected endpoint

The positive cone supplied by the checked endpoint relative bound controls
the actual conditional Gram-channel quadratic for any explicit bounded
spectator family.  The source is the complete projected endpoint V*g_n on
its original carrier.  No channel norm is identified with a variance and no
continuum or scaling conclusion is asserted.
-/

import YMGap.Continuum.SU2QuaternionFamilyChannelCone
import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelRegularity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss
open YMGap.Continuum.SU2QuaternionFamilyChannelCone
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem headCutoff_le_endpointRelativeCutoff (w : Q') :
    headCutoff w ≤ endpointRelativeCutoff w := by
  exact Nat.le_trans (headCutoff_le_relativeCutoff w 32)
    (Nat.le_max_right _ _)

private theorem projectedEndpointSource_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) :=
  familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

/-- One actual selected-link derivative is controlled in the SAME conditional
channel quadratic, for every explicit bounded Nodup spectator schedule. -/
theorem projectedEndpoint_familyChannelDerivative_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (ids : List Nat) (hn : ids.Nodup)
    (hids : ∀ block, block ∈ ids → block < N width)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    let q := projectedEndpointSource w K width (terminalMessage w K width n)
    let d := blockAngularDerivative ((baseLinks width).idxOf selected) i j q
    familyChannelQuadratic (N width) w K ids d ≤
      (endpointRelativeCap w * endpointRelativeCap w) *
        familyChannelQuadratic (N width) w K ids q := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let block := (baseLinks width).idxOf selected
  let d := blockAngularDerivative block i j q
  have P := projectedEndpointRelativeBound hw0 hw1 K width hK n selected hl hs hi hj
  have hp := projectedEndpointSource_supported w K width n
  have hd : SupportedQuaternionBlocks (N width) d := by
    exact angularDerivative_supported_at (by
      have := List.idxOf_lt_length_of_mem hl
      omega) (by
      have := List.idxOf_lt_length_of_mem hl
      omega) hp
  exact familyChannelQuadratic_le_of_cone (N width) hw0 hw1 K
    (Nat.le_trans (headCutoff_le_endpointRelativeCutoff w) hK)
    ids hn hids q d hp hd (endpointRelativeCap w) P.upper P.lower

/-- Summing the six rotations of the same physical link costs only the
literal factor six; it introduces no width- or cutoff-dependent constant. -/
theorem projectedEndpoint_familyChannelAngular_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (ids : List Nat) (hn : ids.Nodup)
    (hids : ∀ block, block ∈ ids → block < N width) :
    let q := projectedEndpointSource w K width (terminalMessage w K width n)
    sixValue (fun i j => familyChannelQuadratic (N width) w K ids
      (blockAngularDerivative ((baseLinks width).idxOf selected) i j q)) ≤
      (6 * (endpointRelativeCap w * endpointRelativeCap w)) *
        familyChannelQuadratic (N width) w K ids q := by
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let c := endpointRelativeCap w * endpointRelativeCap w
  let A := familyChannelQuadratic (N width) w K ids q
  have hsum := sixValue_mono
    (fun i j => familyChannelQuadratic (N width) w K ids
      (blockAngularDerivative ((baseLinks width).idxOf selected) i j q))
    (fun _ _ => c*A) (fun i j hi hj =>
      projectedEndpoint_familyChannelDerivative_le hw0 hw1 K width hK n
        selected hl hs ids hn hids hi hj)
  have hc : sixValue (fun _ _ => c*A) ≈ 6*c*A :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.add (.mul (.var 0) (.var 1)) (.add (.mul (.var 0) (.var 1))
          (.add (.mul (.var 0) (.var 1))
            (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))))
      (.mul (.mul (.const 6) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => c | _ => A)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hc)

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelRegularity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelRegularity.projectedEndpoint_familyChannelDerivative_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelRegularity.projectedEndpoint_familyChannelAngular_le
