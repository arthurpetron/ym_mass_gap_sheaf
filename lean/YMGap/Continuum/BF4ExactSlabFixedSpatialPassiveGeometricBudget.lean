/-
# Passive-channel geometric budget for the original plaquette energy

The spectator heat is first retained in its positive Gram channels.  The
derivative-free plaquette Young estimate is then applied to each resulting
four-block source.  Thus the raw square moments are channel-local rather than
the square of the complete projected source.

The correction below is the SUM of the channel source-increment costs.  It is
not identified with the source-increment cost of the unsplit global source.
The energy-only corollary needs no such identification.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (plaquette spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage energy

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_le (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → left c.2 ≤ right c.2) →
      channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (h c List.mem_cons_self)
        (hw c List.mem_cons_self))
      (channelSum_le left right cs
        (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_add (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => left c + right c) ≈
        channelSum cs left + channelSum cs right
  | [] => Q'.eqv_refl _
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (channelSum_add left right cs))
      (by
        exact poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
          (by decide)
          (fun | 0 => c.1*left c.2 | 1 => c.1*right c.2
               | 2 => channelSum cs left | _ => channelSum cs right))

private theorem channelSum_scale (a : Q') (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => a * value c) ≈ a * channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => value c.2))
        (channelSum_scale a value cs))
      (Q'.eqv_symm (Q'.mul_add_eqv a _ _))

/-- The positive spectator-channel aggregate of the local Young budgets. -/
def passiveGeometricBudget (w : Q') (K width depth : Nat)
    (face : Z4Plaq) : Q' :=
  channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
    geometricBudget w width face
      (plaquetteChannelSource w K width (terminalMessage w K width depth) face c))

/-- The retained correction is channel-local.  No equality with the global
source increment is asserted or used. -/
def passiveChannelIncrement (w : Q') (K width depth : Nat)
    (face : Z4Plaq) : Q' :=
  let f := characterPolynomial (plaquette width face).scalar 1
  channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
    sourceIncrementCost (N width) w K (List.range (N width))
      (plaquetteChannelSource w K width (terminalMessage w K width depth) face c) f)

private theorem channelSource_supported (w : Q') (K width depth : Nat)
    (face : Z4Plaq) (c : GramChannel)
    (hc : c ∈ productChannels (N width) w K (spectatorBlocks width face)) :
    SupportedQuaternionBlocks (N width)
      (plaquetteChannelSource w K width (terminalMessage w K width depth) face c.2) :=
  familyProject_supported (spectatorBlocks width face)
    (supported_polyMul
      (familyProject_supported _ (supported_polyMul
        (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth)))
      (productChannels_supported (N width) w K (spectatorBlocks width face)
        (spectatorBlocks_lt width face) c hc))

private theorem channel_signed_bound {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K width depth : Nat) (hK2 : 2 ≤ K) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (c : GramChannel)
    (hc : c ∈ productChannels (N width) w K (spectatorBlocks width face)) :
    let f := characterPolynomial (plaquette width face).scalar 1
    let b := plaquetteChannelSource w K width
      (terminalMessage w K width depth) face c.2
    (4 : Q') * sourceEnergy (N width) w K (List.range (N width)) b f +
        sourceIncrementCost (N width) w K (List.range (N width)) b f ≤
      (2 : Q') * geometricBudget w width face b := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  let b := plaquetteChannelSource w K width
    (terminalMessage w K width depth) face c.2
  have hb := channelSource_supported w K width depth face c hc
  have hsingle := plaquette_singleEndedCost width face hf w K hK2 b hb
  have hid := four_mul_sourceEnergy_add_increment_eq_two_singleEnded
    (N width) w K (List.range (N width)) (fun _ hi => List.mem_range.mp hi)
    hb (character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left 2 _ _ hsingle))
      (Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
        (plaquetteChannelCost_le_geometricBudget hw0 hw1 width face b hb) (by decide)))

/-- Signed channel-local budget.  Its correction is `passiveChannelIncrement`,
not the unsplit source-increment cost of the complete projected source. -/
theorem padded_terminal_plaquette_passive_signed_geometric_budget {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let f := characterPolynomial (plaquette width face).scalar 1
    (4 : Q') * energy w K width g f +
        passiveChannelIncrement w K width depth face ≤
      (2 : Q') * passiveGeometricBudget w K width depth face := by
  dsimp only
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let E := fun c => sourceEnergy (N width) w K (List.range (N width))
    (plaquetteChannelSource w K width (terminalMessage w K width depth) face c)
    (characterPolynomial (plaquette width face).scalar 1)
  let D := fun c => sourceIncrementCost (N width) w K (List.range (N width))
    (plaquetteChannelSource w K width (terminalMessage w K width depth) face c)
    (characterPolynomial (plaquette width face).scalar 1)
  let G := fun c => geometricBudget w width face
    (plaquetteChannelSource w K width (terminalMessage w K width depth) face c)
  have hE := padded_plaquette_energy_eq_channels w K hwidth depth face hf
  have hpoint : channelSum cs (fun c => (4 : Q')*E c + D c) ≤
      channelSum cs (fun c => (2 : Q')*G c) :=
    channelSum_le _ _ cs (productChannels_nonnegative (N width) hw0 K _)
      (fun c hc => channel_signed_bound hw0 hw1 K width depth hK2 face
        (spatialFaces_mono (Nat.le_of_lt hwidth) hf) c hc)
  have hl : (4 : Q') * energy w K width (terminalMessage w K width depth)
      (characterPolynomial (plaquette width face).scalar 1) + channelSum cs D ≈
      channelSum cs (fun c => (4 : Q')*E c + D c) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left 4 _ _ hE))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (channelSum_scale 4 E cs)))
        (Q'.eqv_symm (channelSum_add (fun c => (4 : Q')*E c) D cs)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hpoint (Q'.le_of_eqv (channelSum_scale 2 G cs)))

/-- Positive-kernel consequence with all spectator heat retained in the
channel weights.  Only the four observable blocks remain in each source. -/
theorem padded_terminal_plaquette_passive_energy_geometric_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let f := characterPolynomial (plaquette width face).scalar 1
    (2 : Q') * energy w K width g f ≤
      passiveGeometricBudget w K width depth face := by
  dsimp only
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let E := fun c => sourceEnergy (N width) w K (List.range (N width))
    (plaquetteChannelSource w K width (terminalMessage w K width depth) face c)
    (characterPolynomial (plaquette width face).scalar 1)
  let G := fun c => geometricBudget w width face
    (plaquetteChannelSource w K width (terminalMessage w K width depth) face c)
  have hE := padded_plaquette_energy_eq_channels w K hwidth depth face hf
  have hpoint : channelSum cs (fun c => (2 : Q')*E c) ≤ channelSum cs G :=
    channelSum_le _ _ cs
      (productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K _)
      (fun c hc => by
        let b := plaquetteChannelSource w K width
          (terminalMessage w K width depth) face c.2
        have hb := channelSource_supported w K width depth face c hc
        exact Q'.le_trans' _ _ _
          (two_mul_sourceEnergy_le_singleEndedCost (N width) hw0 hw1 K hK
            (List.range (N width)) (fun _ hi => List.mem_range.mp hi) hb
            (character_supported
              (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1))
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv (plaquette_singleEndedCost width face
              (spatialFaces_mono (Nat.le_of_lt hwidth) hf) w K hK2 b hb))
            (plaquetteChannelCost_le_geometricBudget (Q'.le_of_lt hw0)
              (Q'.le_of_lt hw1) width face b hb)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 2 _ _ hE)
      (Q'.eqv_symm (channelSum_scale 2 E cs)))) hpoint

end YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget.passiveGeometricBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget.passiveChannelIncrement
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget.padded_terminal_plaquette_passive_signed_geometric_budget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget.padded_terminal_plaquette_passive_energy_geometric_budget
