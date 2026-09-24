/-
# Original plaquette energy with spectator heat retained exactly

The first projection removes the actual inactive fringe, as already proved.
The second projection integrates each explicitly computed Gram-channel source
over blocks untouched by the literal plaquette. Their heat factors remain in
the channel weights and sources; no bulk Taylor expansion is substituted.

The same finite identity preserves odd-marginal moments and hence the original
mass and centering. Channel sources can be signed and are NOT declared to be
probability laws. The total budget still needs a SAME-variance/scaling bound.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage

private theorem projected_supported (w : Q') (K width : Nat) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) :
    SupportedQuaternionBlocks (N width) (projectedEndpointSource w K width g) :=
  familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width) hg)

/-- The exact fringe-projected endpoint source, with a computed spectator
channel inserted BEFORE integrating the remaining spectator variables. -/
def plaquetteChannelSource (w : Q') (K width : Nat) (g : RatPoly)
    (face : Z4Plaq) (c : RatPoly) : RatPoly :=
  channelSource (spectatorBlocks width face) (projectedEndpointSource w K width g) c

/-- Exact moment identity on the original odd-time marginal. The same p is
retained in every channel; no separate channel centering is performed. -/
theorem oddMoment_eq_plaquette_channels (w : Q') (K width depth : Nat)
    (face : Z4Plaq) (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p)
    (hfringe : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i p)
    (hspectator : ∀ i, i ∈ spectatorBlocks width face → QuaternionBlockIndependent i p) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width depth) p) ≈
      channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
        sourceMoment (N width) w K (List.range (N width))
          (plaquetteChannelSource w K width (terminalMessage w K width depth) face c) p) :=
  Q'.eqv_trans _ _ _ (oddMoment_projected_source w K width depth p hp hfringe)
    (sourceMoment_projected_channels (N width) w K
      (observableBlocks width face) (spectatorBlocks width face)
      (observableBlocks_lt width face) (spectatorBlocks_lt width face)
      (spectator_not_observable width face) (spectator_observable_cover width face)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) p
      (projected_supported w K width _ (terminalMessage_supported w K width depth)) hp hspectator)

/-- The literal plaquette supplies the independence guard for all untouched
blocks. Strict padding supplies the original inactive-fringe guard. -/
theorem padded_plaquette_energy_eq_channels (w : Q') (K : Nat) {base width : Nat}
    (hwidth : base < width) (depth : Nat) (face : Z4Plaq) (hface : face ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let f := characterPolynomial (plaquette width face).scalar 1
    energy w K width g f ≈
      channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
        sourceEnergy (N width) w K (List.range (N width))
          (plaquetteChannelSource w K width g face c) f) := by
  let g := terminalMessage w K width depth
  let f := characterPolynomial (plaquette width face).scalar 1
  have hg := terminalMessage_supported w K width depth
  have hf := SU2QuaternionRelativeHeatPairGeometry.character_supported
    (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  exact Q'.eqv_trans _ _ _ (energy_projected_source w K width g f hg hf
    (plaquette_fringe_independent_after_padding hwidth face hface))
    (sourceEnergy_projected_channels (N width) w K
      (observableBlocks width face) (spectatorBlocks width face)
      (observableBlocks_lt width face) (spectatorBlocks_lt width face)
      (spectator_not_observable width face) (spectator_observable_cover width face)
      (projectedEndpointSource w K width g) f (projected_supported w K width g hg) hf
      (plaquette_spectator_independent width face))

/-- Original-action consumer of the exact spectator-channel Taylor estimate.
No uniform bound on this channel sum or ratio to the SAME variance is asserted. -/
theorem padded_plaquette_energy_le_channel_budgets {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : sufficientCutoff w ≤ K) (depth : Nat)
    (face : Z4Plaq) (hface : face ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let f := characterPolynomial (plaquette width face).scalar 1
    energy w K width g f ≤
      channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
        ((1 : Q')-w) * weightedAngularEnergy (N width-1)
          (plaquetteChannelSource w K width g face c) f +
        (((1 : Q')-w)*((1 : Q')-w)) * pairBudget (N width-1)
          (plaquetteChannelSource w K width g face c)
          (polyMul (plaquetteChannelSource w K width g face c) (polyMul f f))) := by
  let g := terminalMessage w K width depth
  let f := characterPolynomial (plaquette width face).scalar 1
  have hf' := spatialFaces_mono (Nat.le_of_lt hwidth) hface
  have hl : (face.1, (dirsOf face.2).1) ∈ baseLinks width :=
    face_link_mem_base hf' (by simp [edgesOf])
  have hb : 0 < N width := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl)
  have hN : N width-1+1 = N width := Nat.sub_add_cancel hb
  have hg := terminalMessage_supported w K width depth
  have hf := SU2QuaternionRelativeHeatPairGeometry.character_supported
    (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have h := sourceEnergy_le_projected_channel_budgets (N width-1) hw0 hw1 K hK
    (observableBlocks width face) (spectatorBlocks width face)
    (by simpa only [hN] using observableBlocks_lt width face)
    (by simpa only [hN] using spectatorBlocks_lt width face)
    (spectator_not_observable width face)
    (by simpa only [hN] using spectator_observable_cover width face)
    (projectedEndpointSource w K width g) f
    (by simpa only [hN] using projected_supported w K width g hg)
    (by simpa only [hN] using hf) (plaquette_spectator_independent width face)
  simp only [hN] at h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (energy_projected_source w K width g f hg hf
      (plaquette_fringe_independent_after_padding hwidth face hface))) h

end YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels.plaquetteChannelSource
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels.oddMoment_eq_plaquette_channels
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels.padded_plaquette_energy_eq_channels
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels.padded_plaquette_energy_le_channel_budgets
