/-
# Retained source responses after spectator integration

The computed passive channels preserve the ORIGINAL plaquette energy.
Their source-increment costs and responses belong to the integrated sources,
not to the unsplit source. The exact channel Young cost contracts to the
original cost without replacing its signed heat coefficients by a majorant.

The result retains the sum of channel response squares. No nonzero response,
variance-relative fraction, stationary source or physical scaling is assumed.
The comparison is for ONE literal face, not a facewise bound on cross terms
of an arbitrary signed plaquette family.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChannelYoungCostComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungCancellation
import YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveSourceCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceEnergy)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (plaquette spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveGeometricBudget (passiveChannelIncrement)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments
  (plaquetteChannelSource_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungCancellation
open YMGap.Continuum.BF4ExactSlabFixedSpatialChannelYoungCostComparison
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage
attribute [local irreducible] plaquetteChannelSource projectedEndpointSource
  sourceResponse plaquetteChannelCost sourceIncrementCost

private theorem sum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel, (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (sum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem sum_le (left right : RatPoly → Q') :
    ∀ cs : List GramChannel, (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → left c.2 ≤ right c.2) → channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (h c List.mem_cons_self) (hw c List.mem_cons_self))
      (sum_le left right cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem sum_add (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => left c+right c) ≈ channelSum cs left+channelSum cs right
  | [] => Q'.eqv_refl _
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (sum_add left right cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide) (fun | 0 => c.1*left c.2 | 1 => c.1*right c.2
                         | 2 => channelSum cs left | _ => channelSum cs right))

private theorem sum_scale (a : Q') (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => a*value c) ≈ a*channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => value c.2)) (sum_scale a value cs))
      (Q'.eqv_symm (Q'.mul_add_eqv a _ _))

/-- The computed nonnegative response sum is quadratic in the COMPLETE
terminal source. It is not the square of the original interacting mean. -/
def passiveResponseSquares (w : Q') (K width depth : Nat) (face : Z4Plaq) : Q' :=
  channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
    let b := plaquetteChannelSource w K width (terminalMessage w K width depth) face c
    sourceResponse w width face b * sourceResponse w width face b)

/-- Exact channel Young identity, with the SAME original temporal energy. -/
theorem padded_terminal_channel_young_identity (w : Q') (K : Nat) (hK2 : 2 ≤ K)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let f := characterPolynomial (plaquette width face).scalar 1
    4*energy w K width (terminalMessage w K width depth) f +
      passiveChannelIncrement w K width depth face ≈
        2*channelYoungCost width face w K q := by
  dsimp only
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let b := fun c => plaquetteChannelSource w K width (terminalMessage w K width depth) face c
  let f := characterPolynomial (plaquette width face).scalar 1
  let E := fun c => sourceEnergy (N width) w K (List.range (N width)) (b c) f
  let D := fun c => sourceIncrementCost (N width) w K (List.range (N width)) (b c) f
  let C := fun c => plaquetteChannelCost width face w (b c)
  have hE := padded_plaquette_energy_eq_channels w K hwidth depth face hf
  have hpoint : channelSum cs (fun c => 4*E c+D c) ≈ channelSum cs (fun c => 2*C c) :=
    sum_congr _ _ cs (fun c hc => by
      have hb := plaquetteChannelSource_supported w K width _
        (terminalMessage_supported w K width depth) face c hc
      exact Q'.eqv_trans _ _ _
        (four_mul_sourceEnergy_add_increment_eq_two_singleEnded (N width) w K
          (List.range (N width)) (fun _ hi => List.mem_range.mp hi) hb
          (character_supported (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1))
        (Q'.mul_eqv_congr_left 2 _ _ (plaquette_singleEndedCost width face
          (spatialFaces_mono (Nat.le_of_lt hwidth) hf) w K hK2 _ hb)))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left 4 _ _ hE))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (sum_scale 4 E cs).symm)
      (Q'.eqv_trans _ _ _ (sum_add (fun c => 4*E c) D cs).symm
        (Q'.eqv_trans _ _ _ hpoint (by
          simpa only [channelYoungCost, plaquetteChannelSource, C, b, cs] using
            sum_scale 2 C cs))))

/-- Every computed channel supplies its own favorable response square. -/
theorem passive_responses_le_increment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width depth : Nat) (hK1 : 1 ≤ K) (hK : headCutoff w ≤ K)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    passiveResponseSquares w K width depth face ≤ passiveChannelIncrement w K width depth face := by
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let b := fun c => plaquetteChannelSource w K width (terminalMessage w K width depth) face c
  let f := characterPolynomial (plaquette width face).scalar 1
  let R := fun c => sourceResponse w width face (b c)*sourceResponse w width face (b c)
  let D := fun c => sourceIncrementCost (N width) w K (List.range (N width)) (b c) f
  have hp : ∀ c, c ∈ cs → R c.2 ≤ D c.2 := fun c hc =>
    sourceIncrement_ge_response_square hw0 hw1 K width hK1 hK face hf _
      (plaquetteChannelSource_supported w K width _
        (terminalMessage_supported w K width depth) face c hc)
  exact sum_le R D cs (productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K _) hp

/-- Spectator heat stays in the computed response and cost, without a global
raw q^2/partition cap. Strict gain still requires a quantitative response. -/
theorem padded_terminal_passive_retained_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let f := characterPolynomial (plaquette width face).scalar 1
    4*energy w K width (terminalMessage w K width depth) f +
      passiveResponseSquares w K width depth face ≤ 2*channelYoungCost width face w K q := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left _ _ _ (passive_responses_le_increment hw0 hw1 K width depth
      (by omega) hK face (spatialFaces_mono (Nat.le_of_lt hwidth) hf)))
    (Q'.le_of_eqv (padded_terminal_channel_young_identity w K hK2 hwidth depth face hf))

/-- The smaller exact channel cost bounds the SAME original single-ended
cost; no facewise composition for signed families is inferred. -/
theorem padded_terminal_passive_retained_raw_cost {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let f := characterPolynomial (plaquette width face).scalar 1
    4*energy w K width (terminalMessage w K width depth) f +
      passiveResponseSquares w K width depth face ≤ 2*plaquetteChannelCost width face w q := by
  dsimp only
  have hq : SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) := by
    unfold projectedEndpointSource
    exact familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  exact Q'.le_trans' _ _ _
    (padded_terminal_passive_retained_square hw0 hw1 K hK2 hK hwidth depth face hf)
    (Q'.mul_le_mul_of_nonneg_left _ _ 2
      (channelYoungCost_le_raw width face (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K _ hq)
      (by decide))

/-- The discarded spectator contribution is exactly twice the reduction
of the one-ended cost. The integrated and unsplit increments are NOT equal. -/
theorem padded_terminal_increment_difference (w : Q') (K : Nat) (hK2 : 2 ≤ K)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let f := characterPolynomial (plaquette width face).scalar 1
    sourceIncrementCost (N width) w K (List.range (N width)) q f -
      passiveChannelIncrement w K width depth face ≈
        2*(plaquetteChannelCost width face w q-channelYoungCost width face w K q) := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := characterPolynomial (plaquette width face).scalar 1
  let E := energy w K width (terminalMessage w K width depth) f
  let D := sourceIncrementCost (N width) w K (List.range (N width)) q f
  let Dc := passiveChannelIncrement w K width depth face
  let C := plaquetteChannelCost width face w q
  let Cc := channelYoungCost width face w K q
  have ho : 4*E+D ≈ 2*C :=
    padded_terminal_plaquette_young_channels w K hK2 hwidth depth face hf
  have hc : 4*E+Dc ≈ 2*Cc :=
    padded_terminal_channel_young_identity w K hK2 hwidth depth face hf
  have hl : D-Dc ≈ (4*E+D)-(4*E+Dc) :=
    poly_identity_of_normal_eq (.add (.var 1) (.neg (.var 2)))
      (.add (.add (.mul (.const 4) (.var 0)) (.var 1))
        (.neg (.add (.mul (.const 4) (.var 0)) (.var 2))))
      (by decide) (fun | 0 => E | 1 => D | _ => Dc)
  have hr : 2*C-2*Cc ≈ 2*(C-Cc) :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 0)) (.neg (.mul (.const 2) (.var 1))))
      (.mul (.const 2) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => C | _ => Cc)
  exact Q'.eqv_trans _ _ _ hl
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ho (Q'.neg_eqv_congr _ _ hc)) hr)

/-- The integrated increment is no larger than the original increment.
This is a coefficient-one finite comparison, not a variance-relative rate. -/
theorem padded_terminal_channel_increment_le_original {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let f := characterPolynomial (plaquette width face).scalar 1
    passiveChannelIncrement w K width depth face ≤
      sourceIncrementCost (N width) w K (List.range (N width)) q f := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := characterPolynomial (plaquette width face).scalar 1
  have hq : SupportedQuaternionBlocks (N width) q := by
    unfold q projectedEndpointSource
    exact familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  have hC := channelYoungCost_le_raw width face hw0 hw1 K q hq
  have hn : (0 : Q') ≤ 2*(plaquetteChannelCost width face w q-channelYoungCost width face w K q) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le hC)
  have hid := padded_terminal_increment_difference w K hK2 hwidth depth face hf
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.ge_of_eqv hid))

#print axioms passiveResponseSquares
#print axioms padded_terminal_channel_young_identity
#print axioms passive_responses_le_increment
#print axioms padded_terminal_passive_retained_square
#print axioms padded_terminal_passive_retained_raw_cost
#print axioms padded_terminal_increment_difference
#print axioms padded_terminal_channel_increment_le_original

end YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveSourceCancellation
