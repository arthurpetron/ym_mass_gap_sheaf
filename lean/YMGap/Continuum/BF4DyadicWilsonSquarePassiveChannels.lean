/-
# Original growing-square energy and moments with spectator heat retained

The active slots are those of the actual padded dyadic Wilson word. Every
other heat factor remains in the computed Gram weights and projected channel
sources. The same identity preserves the original odd mass and all admissible
insertions, without separate channel normalization or channelwise centering.

This is finite exact algebra. It supplies no uniform source-square/partition
comparison or SAME centered-variance estimate along a scaling trajectory.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope
import YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels

namespace YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredHaarTelescope (mass_oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage

private theorem projected_supported (w : Q') (K width : Nat) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) :
    SupportedQuaternionBlocks (N width) (projectedEndpointSource w K width g) :=
  familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width) hg)

/-- The full original projected endpoint source in a computed spectator channel. -/
def squareChannelSource (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g c : RatPoly) : RatPoly :=
  channelSource (spectatorBlocks scale width hwidth)
    (projectedEndpointSource w K width g) c

theorem squareChannelSource_supported (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) (c : Q' × RatPoly)
    (hc : c ∈ productChannels (N width) w K (spectatorBlocks scale width hwidth)) :
    SupportedQuaternionBlocks (N width)
      (squareChannelSource w K scale width hwidth g c.2) :=
  familyProject_supported (spectatorBlocks scale width hwidth)
    (supported_polyMul (projected_supported w K width g hg)
      (productChannels_supported (N width) w K (spectatorBlocks scale width hwidth)
        (spectatorBlocks_lt scale width hwidth) c hc))

theorem squareChannelSource_spectator_independent (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g c : RatPoly) (i : Nat)
    (hi : i ∈ spectatorBlocks scale width hwidth) :
    QuaternionBlockIndependent i (squareChannelSource w K scale width hwidth g c) :=
  channelSource_independent (spectatorBlocks scale width hwidth)
    (projectedEndpointSource w K width g) c i hi

/-- The same insertion is retained in every channel of the original odd marginal. -/
theorem oddMoment_eq_square_channels (scale width : Nat)
    (hwidth : side scale < width) (w : Q') (K depth : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p)
    (hfringe : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i p)
    (hspectator : ∀ i, i ∈ spectatorBlocks scale width hwidth →
      QuaternionBlockIndependent i p) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width depth) p) ≈
      channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
        (fun c => sourceMoment (N width) w K (List.range (N width))
          (squareChannelSource w K scale width hwidth (terminalMessage w K width depth) c) p) :=
  Q'.eqv_trans _ _ _ (oddMoment_projected_source w K width depth p hp hfringe)
    (sourceMoment_projected_channels (N width) w K
      (observableBlocks scale width hwidth) (spectatorBlocks scale width hwidth)
      (observableBlocks_lt scale width hwidth) (spectatorBlocks_lt scale width hwidth)
      (spectator_not_observable scale width hwidth)
      (spectator_observable_cover scale width hwidth)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) p
      (projected_supported w K width _ (terminalMessage_supported w K width depth))
      hp hspectator)

/-- Exact original terminal energy. Both independence guards are derived for
the actual padded square, not assumed for a replacement observable. -/
theorem paddedSquare_energy_eq_channels (scale width : Nat)
    (hwidth : side scale < width) (w : Q') (K depth : Nat) :
    let g := terminalMessage w K width depth
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    energy w K width g f ≈
      channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
        (fun c => sourceEnergy (N width) w K (List.range (N width))
          (squareChannelSource w K scale width hwidth g c) f) := by
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  have hg := terminalMessage_supported w K width depth
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  exact Q'.eqv_trans _ _ _
    (energy_projected_source w K width g f hg hf
      (paddedSquare_fringe_independent scale width hwidth))
    (sourceEnergy_projected_channels (N width) w K
      (observableBlocks scale width hwidth) (spectatorBlocks scale width hwidth)
      (observableBlocks_lt scale width hwidth) (spectatorBlocks_lt scale width hwidth)
      (spectator_not_observable scale width hwidth)
      (spectator_observable_cover scale width hwidth)
      (projectedEndpointSource w K width g) f (projected_supported w K width g hg) hf
      (sourceCharacter_spectator_independent scale width hwidth))

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List (Q' × RatPoly),
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem sourceMoment_congr (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) {a b : RatPoly} (hab : RatPolyCoeffEqv a b) (p : RatPoly) :
    sourceMoment n w K ids a p ≈ sourceMoment n w K ids b p :=
  haar_of_coeff ((hab.mul_right p).mul (productMap_congr n w K ids hab))

/-- Only the actual word's active heat blocks remain in each channel moment. -/
theorem squareChannel_moment_active (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) (c : Q' × RatPoly)
    (hc : c ∈ productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p)
    (hind : ∀ i, i ∈ spectatorBlocks scale width hwidth → QuaternionBlockIndependent i p) :
    sourceMoment (N width) w K (List.range (N width))
        (squareChannelSource w K scale width hwidth g c.2) p ≈
      sourceMoment (N width) w K (observableBlocks scale width hwidth)
        (squareChannelSource w K scale width hwidth g c.2) p := by
  let b := squareChannelSource w K scale width hwidth g c.2
  have hfixed : RatPolyCoeffEqv (familyProject (spectatorBlocks scale width hwidth) b) b :=
    familyProject_fixed (spectatorBlocks scale width hwidth) b
      (squareChannelSource_spectator_independent w K scale width hwidth g c.2)
  exact (Q'.eqv_trans _ _ _
    (sourceMoment_project (N width) w K
      (observableBlocks scale width hwidth) (spectatorBlocks scale width hwidth)
      (observableBlocks_lt scale width hwidth) (spectatorBlocks_lt scale width hwidth)
      (spectator_not_observable scale width hwidth)
      (spectator_observable_cover scale width hwidth)
      b p (squareChannelSource_supported w K scale width hwidth g hg c hc) hp hind)
    (sourceMoment_congr (N width) w K (List.range (N width)) hfixed p)).symm

/-- This one identity retains the original partition, mean and second moment;
it does not identify the channel raw square with any of those quantities. -/
theorem oddMoment_eq_active_square_channels (scale width : Nat)
    (hwidth : side scale < width) (w : Q') (K depth : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p)
    (hfringe : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i p)
    (hspectator : ∀ i, i ∈ spectatorBlocks scale width hwidth →
      QuaternionBlockIndependent i p) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width depth) p) ≈
      channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
        (fun c => sourceMoment (N width) w K (observableBlocks scale width hwidth)
          (squareChannelSource w K scale width hwidth (terminalMessage w K width depth) c) p) :=
  Q'.eqv_trans _ _ _
    (oddMoment_eq_square_channels scale width hwidth w K depth p hp hfringe hspectator)
    (channelSum_congr _ _ _ (fun c hc =>
      squareChannel_moment_active w K scale width hwidth _
        (terminalMessage_supported w K width depth) c hc p hp hspectator))

/-- The physical odd mass is the sum of active HEAT moments, not source squares. -/
theorem oddMass_eq_active_square_channels (scale width : Nat)
    (hwidth : side scale < width) (w : Q') (K depth : Nat) :
    oddMass w K width depth ≈
      channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
        (fun c => sourceMoment (N width) w K (observableBlocks scale width hwidth)
          (squareChannelSource w K scale width hwidth (terminalMessage w K width depth) c)
          polyOne) :=
  Q'.eqv_trans _ _ _ (mass_oddMass w K width depth).symm
    (Q'.eqv_trans _ _ _
      (haar_of_coeff (blocks := N width) (RatPolyCoeffEqv.mul_one
        (marginalWeight w K width depth))).symm
      (oddMoment_eq_active_square_channels scale width hwidth w K depth polyOne
        (supported_one (N width)) (fun i _ => quaternionBlockIndependent_polyOne i)
        (fun i _ => quaternionBlockIndependent_polyOne i)))

#print axioms squareChannelSource
#print axioms squareChannelSource_supported
#print axioms squareChannelSource_spectator_independent
#print axioms oddMoment_eq_square_channels
#print axioms paddedSquare_energy_eq_channels
#print axioms squareChannel_moment_active
#print axioms oddMoment_eq_active_square_channels
#print axioms oddMass_eq_active_square_channels

end YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
