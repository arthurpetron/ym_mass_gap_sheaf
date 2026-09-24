/-
# SAME odd-marginal moments with only the plaquette heat blocks active

The computed spectator channels retain all spectator heat. Each channel source
is independent of spectator coordinates, so its full product-heat moment equals
the moment using only the physical plaquette block list. This is an exact
identity with the ORIGINAL odd marginal, including its partition and mean.

No raw-square/interacting-moment inequality or scaling-uniform comparison is
claimed. In particular a selected productMap is not conditional heat: its
unselected coordinates are Haar-averaged. Independence is what permits the
reduction below.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels
import YMGap.Continuum.Z4CanonicalPolymerUniverse

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels
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
attribute [local irreducible] baseLinks terminalMessage

/-- A genuine spatial face retains four distinct physical block slots. -/
theorem faceSlots_nodup (width : Nat) (face : Z4Plaq)
    (hf : face ∈ BF4ExactSlabFixedSpatialFacePlacement.spatialFaces width) :
    (faceSlots width face).Nodup :=
  CayleyPruferInjection.nodup_map_of_injOn _ _
    (Z4UnitCubeIncidenceParity.edgesOf_nodup face)
    (fun _ ha _ hb he => BF4ExactSlabTemporalGaugeLedger.idxOf_injective_on_members
      (BF4ExactSlabFixedSpatialFaceSelection.face_link_mem_base hf ha)
      (BF4ExactSlabFixedSpatialFaceSelection.face_link_mem_base hf hb) he)

/-- The reduced heat list has exactly four blocks, independently of width. -/
theorem observableBlocks_length (width : Nat) (face : Z4Plaq)
    (hf : face ∈ BF4ExactSlabFixedSpatialFacePlacement.spatialFaces width) :
    (observableBlocks width face).length = 4 := by
  have hlt : ∀ i, i ∈ faceSlots width face → i < N width := by
    intro i hi
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hi
    exact List.idxOf_lt_length_of_mem
      (BF4ExactSlabFixedSpatialFaceSelection.face_link_mem_base hf hl)
  have hp := Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
    (observableBlocks width face) (faceSlots width face)
    (List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width)))
    (faceSlots_nodup width face hf) (fun i => by
      constructor
      · intro hi
        exact of_decide_eq_true (List.mem_filter.mp hi).2
      · intro hi
        exact List.mem_filter.mpr ⟨List.mem_range.mpr (hlt i hi), by simp [hi]⟩)
  simpa only [faceSlots, List.length_map, edgesOf, List.length_cons, List.length_nil]
    using hp.length_eq

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

/-- The actual projected channel source has no spectator dependence. -/
theorem plaquetteChannelSource_spectator_independent
    (w : Q') (K width : Nat) (g : RatPoly) (face : Z4Plaq) (c : RatPoly)
    (i : Nat) (hi : i ∈ spectatorBlocks width face) :
    QuaternionBlockIndependent i (plaquetteChannelSource w K width g face c) :=
  channelSource_independent (spectatorBlocks width face)
    (projectedEndpointSource w K width g) c i hi

/-- Only computed channels are used; no unsupported source is inserted. -/
theorem plaquetteChannelSource_supported
    (w : Q') (K width : Nat) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) (face : Z4Plaq)
    (c : Q' × RatPoly)
    (hc : c ∈ productChannels (N width) w K (spectatorBlocks width face)) :
    SupportedQuaternionBlocks (N width)
      (plaquetteChannelSource w K width g face c.2) :=
  familyProject_supported (spectatorBlocks width face)
    (supported_polyMul
      (familyProject_supported (fringeBlocks width)
        (supported_polyMul (spatialWeight_supported w K width) hg))
      (productChannels_supported (N width) w K (spectatorBlocks width face)
        (spectatorBlocks_lt width face) c hc))

/-- Full and plaquette-only heat give the SAME inserted moment on each
computed channel source. The insertion must also be spectator-independent. -/
theorem plaquetteChannel_moment_active
    (w : Q') (K width : Nat) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) (face : Z4Plaq)
    (c : Q' × RatPoly)
    (hc : c ∈ productChannels (N width) w K (spectatorBlocks width face))
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p)
    (hind : ∀ i, i ∈ spectatorBlocks width face → QuaternionBlockIndependent i p) :
    sourceMoment (N width) w K (List.range (N width))
        (plaquetteChannelSource w K width g face c.2) p ≈
      sourceMoment (N width) w K (observableBlocks width face)
        (plaquetteChannelSource w K width g face c.2) p := by
  let b := plaquetteChannelSource w K width g face c.2
  have hfixed : RatPolyCoeffEqv (familyProject (spectatorBlocks width face) b) b :=
    familyProject_fixed (spectatorBlocks width face) b
      (plaquetteChannelSource_spectator_independent w K width g face c.2)
  exact (Q'.eqv_trans _ _ _
    (sourceMoment_project (N width) w K
      (observableBlocks width face) (spectatorBlocks width face)
      (observableBlocks_lt width face) (spectatorBlocks_lt width face)
      (spectator_not_observable width face) (spectator_observable_cover width face)
      b p (plaquetteChannelSource_supported w K width g hg face c hc) hp hind)
    (sourceMoment_congr (N width) w K (List.range (N width)) hfixed p)).symm

/-- ORIGINAL partition, mean and second moment all use this one identity.
No channelwise recentering and no replacement normalization is performed. -/
theorem oddMoment_eq_active_plaquette_channels
    (w : Q') (K width depth : Nat) (face : Z4Plaq)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p)
    (hfringe : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i p)
    (hspectator : ∀ i, i ∈ spectatorBlocks width face → QuaternionBlockIndependent i p) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width depth) p) ≈
      channelSum (productChannels (N width) w K (spectatorBlocks width face))
        (fun c => sourceMoment (N width) w K (observableBlocks width face)
          (plaquetteChannelSource w K width (terminalMessage w K width depth) face c) p) :=
  Q'.eqv_trans _ _ _
    (oddMoment_eq_plaquette_channels w K width depth face p hp hfringe hspectator)
    (channelSum_congr _ _ _ (fun c hc =>
      plaquetteChannel_moment_active w K width _ (terminalMessage_supported w K width depth)
        face c hc p hp hspectator))

end YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments.plaquetteChannelSource_spectator_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments.faceSlots_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments.observableBlocks_length
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments.plaquetteChannelSource_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments.plaquetteChannel_moment_active
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments.oddMoment_eq_active_plaquette_channels
