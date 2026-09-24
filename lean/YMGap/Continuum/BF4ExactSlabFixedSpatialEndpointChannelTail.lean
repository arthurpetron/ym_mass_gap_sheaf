/-
# Harmonic tails inside the actual endpoint Gram channels

For an active link outside an explicit spectator family, the selected-link
high harmonic part is taken separately in every actual conditional channel.
The exact channel angular identity and the endpoint cone estimate pay for the
sum by the SAME conditional quadratic of the complete projected endpoint.
No channel polynomial is assumed positive, and no partial product map replaces
the conditional channel expansion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelRegularity
import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointSpectralTail
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
import YMGap.Continuum.SU2QuaternionChannelAngularContraction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelTail

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
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointSpectralTail
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelRegularity
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
  (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularSquare)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

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

private theorem channelSum_scale (a : Q') (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun p => a * value p) ≈ a * channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_scale a value cs))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.var 3)))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3)))
        (by decide)
        (fun | 0 => c.1 | 1 => a | 2 => value c.2
             | _ => channelSum cs value))

private theorem channelSum_nonnegative (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → (0 : Q') ≤ value c.2) →
      (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, hv => Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (QPoly.q_zero_add_eqv 0))
      (Q'.add_le_add
        (Q'.mul_nonneg _ _ (hw c List.mem_cons_self)
          (hv c List.mem_cons_self))
        (channelSum_nonnegative value cs
          (fun d hd => hw d (List.mem_cons_of_mem c hd))
          (fun d hd => hv d (List.mem_cons_of_mem c hd))))

private theorem projectedEndpointSource_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) :=
  familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

private theorem familyChannelQuadratic_nonnegative (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (q : RatPoly)
    (hq : SupportedQuaternionBlocks n q) :
    (0 : Q') ≤ familyChannelQuadratic n w K ids q := by
  let cs := productChannels n w K ids
  apply channelSum_nonnegative (fun c => quaternionHaar n
    (polyMul (familyProject ids (polyMul q c))
      (familyProject ids (polyMul q c)))) cs
    (productChannels_nonnegative n (Q'.le_of_lt hw0) K ids)
  intro c hc
  have hs : SupportedQuaternionBlocks n (familyProject ids (polyMul q c.2)) :=
    familyProject_supported ids (supported_polyMul hq
      (productChannels_supported n w K ids hids c hc))
  exact (Certificate.square _ hs).haar_nonnegative

/-- At one actual active link outside the selected spectator family, the sum
of the channelwise computed high harmonic squares is epsilon-small relative
to the SAME conditional quadratic of the complete projected endpoint. -/
theorem projectedEndpoint_familyChannel_highTail_small {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (ids : List Nat) (hn : ids.Nodup)
    (hids : ∀ block, block ∈ ids → block < N width)
    (hnot : (baseLinks width).idxOf selected ∉ ids)
    (epsilon : Q') (he : (0 : Q') < epsilon) (L : Nat)
    (hL : endpointTailDegree w epsilon he ≤ L) :
    let q := projectedEndpointSource w K width (terminalMessage w K width n)
    let block := (baseLinks width).idxOf selected
    channelSum (productChannels (N width) w K ids) (fun c =>
      quaternionHaar (N width) (polyMul
        (selectedSpectralHighPart (N width) block
          (List.idxOf_lt_length_of_mem hl) L (channelSource ids q c))
        (selectedSpectralHighPart (N width) block
          (List.idxOf_lt_length_of_mem hl) L (channelSource ids q c)))) ≤
      epsilon * familyChannelQuadratic (N width) w K ids q := by
  let blocks := N width
  let block := (baseLinks width).idxOf selected
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let cs := productChannels blocks w K ids
  let a := Q'.ofNat ((L+1)*(L+3))
  let tail := fun c : RatPoly => quaternionHaar blocks (polyMul
    (selectedSpectralHighPart blocks block (List.idxOf_lt_length_of_mem hl) L
      (channelSource ids q c))
    (selectedSpectralHighPart blocks block (List.idxOf_lt_length_of_mem hl) L
      (channelSource ids q c)))
  let angular := fun c : RatPoly =>
    quaternionHaar blocks (blockAngularSquare block (channelSource ids q c))
  let A := familyChannelQuadratic blocks w K ids q
  have hq := projectedEndpointSource_supported w K width n
  have hweights := productChannels_nonnegative blocks (Q'.le_of_lt hw0) K ids
  have hthreshold : a * channelSum cs tail ≤ channelSum cs angular := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (channelSum_scale a tail cs)) ?_
    apply channelSum_le _ _ cs hweights
    intro c hc
    exact selectedSpectralHighPart_threshold_le_energy blocks block
      (List.idxOf_lt_length_of_mem hl) L (channelSource ids q c.2)
      (familyProject_supported ids (supported_polyMul hq
        (productChannels_supported blocks w K ids hids c hc)))
  have hangular : channelSum cs angular ≤
      (6 * (endpointRelativeCap w * endpointRelativeCap w)) * A := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (channelSource_blockAngularSquare_eq blocks w K ids block hnot q)) ?_
    exact projectedEndpoint_familyChannelAngular_le hw0 hw1 K width hK n
      selected hl hs ids hn hids
  have hA : (0 : Q') ≤ A :=
    familyChannelQuadratic_nonnegative blocks hw0 K ids hids q hq
  have hcost : (6 * (endpointRelativeCap w * endpointRelativeCap w)) * A ≤
      (epsilon * a) * A :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (endpointTailDegree_sufficient w epsilon he L hL) hA
  have hmul : a * channelSum cs tail ≤ (epsilon * a) * A :=
    Q'.le_trans' _ _ _ hthreshold (Q'.le_trans' _ _ _ hangular hcost)
  have ha : (0 : Q') < a := by
    change (0 : Int) * 1 < (((L+1)*(L+3) : Nat) : Int) * 1
    simpa only [Int.zero_mul, Int.mul_one] using
      (Int.ofNat_lt.mpr (Nat.mul_pos (by omega : 0 < L+1) (by omega : 0 < L+3)))
  apply Q'.le_of_mul_le_mul_left (c := a) (hc := ha)
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => epsilon | 1 => a | _ => A)))

/-- The preceding channel-tail estimate on the actual complementary family of
a fixed plaquette. Membership in the plaquette observable blocks supplies the
required exclusion from the spectator schedule. -/
theorem projectedEndpoint_plaquetteChannel_highTail_small {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointRelativeCutoff w ≤ K) (n : Nat)
    (face : Z4Plaq) (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (hobs : (baseLinks width).idxOf selected ∈ observableBlocks width face)
    (epsilon : Q') (he : (0 : Q') < epsilon) (L : Nat)
    (hL : endpointTailDegree w epsilon he ≤ L) :
    let q := projectedEndpointSource w K width (terminalMessage w K width n)
    let block := (baseLinks width).idxOf selected
    channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
      quaternionHaar (N width) (polyMul
        (selectedSpectralHighPart (N width) block
          (List.idxOf_lt_length_of_mem hl) L
          (channelSource (spectatorBlocks width face) q c))
        (selectedSpectralHighPart (N width) block
          (List.idxOf_lt_length_of_mem hl) L
          (channelSource (spectatorBlocks width face) q c)))) ≤
      epsilon * familyChannelQuadratic (N width) w K
        (spectatorBlocks width face) q := by
  have hnd : (spectatorBlocks width face).Nodup :=
    List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width))
  have hnot : (baseLinks width).idxOf selected ∉ spectatorBlocks width face := by
    intro hsp
    exact spectator_not_observable width face _ hsp hobs
  exact projectedEndpoint_familyChannel_highTail_small hw0 hw1 K width hK n
    selected hl hs (spectatorBlocks width face) hnd
    (spectatorBlocks_lt width face) hnot epsilon he L hL

#print axioms projectedEndpoint_familyChannel_highTail_small
#print axioms projectedEndpoint_plaquetteChannel_highTail_small

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelTail
