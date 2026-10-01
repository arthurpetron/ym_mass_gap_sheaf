/-
# Spectator responses dominate the original source response

The complete computed spectator response sum is at least the square of the
original Haar source response. This follows from the exact channel mean Gram
pin and Cauchy--Schwarz against the constant vector of the SAME kinetic form.
No channel is assumed positive and no vacuum channel is selected from a list.

Together with the checked exact one-face cost contraction, this supplies two
nonnegative gains in the ORIGINAL terminal energy ceiling. Neither gain is
asserted positive or compared with interacting variance. The cost statement
is for ONE face, not a facewise estimate on a signed family.
-/

import YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveSourceCancellation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveResponseDominance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (plaquette spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels (plaquetteChannelSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit (plaquetteChannelCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungCancellation (sourceResponse)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChannelYoungCostComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveSourceCancellation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  plaquetteChannelSource sourceResponse plaquetteChannelCost

private theorem sum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel, (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (sum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem sum_scale (a : Q') (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => a*value c) ≈ a*channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => value c.2))
        (sum_scale a value cs))
      (Q'.eqv_symm (Q'.mul_add_eqv a _ _))

private theorem response_square_pin (w : Q') (width : Nat) (face : Z4Plaq)
    (q : RatPoly) :
    sourceResponse w width face q * sourceResponse w width face q ≈
      (2*(1 + -(qpow w 12)))*(2*(1 + -(qpow w 12))) *
        (H width (polyMul q (characterPolynomial (plaquette width face).scalar 1)) *
          H width (polyMul q (characterPolynomial (plaquette width face).scalar 1))) := by
  unfold sourceResponse
  exact poly_identity_of_normal_eq
    (.mul (.mul (.const 2) (.mul (.var 0) (.var 1)))
      (.mul (.const 2) (.mul (.var 0) (.var 1))))
    (.mul (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
      (.mul (.var 1) (.var 1))) (by decide)
    (fun | 0 => 1 + -(qpow w 12)
         | _ => H width (polyMul q (characterPolynomial (plaquette width face).scalar 1)))

/-- Exact sum of response squares for any supported source of one face.
All spectator heat is retained before the square is formed. -/
theorem channel_response_squares_pin (w : Q') (K width : Nat)
    (face : Z4Plaq) (q : RatPoly) :
    channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
      sourceResponse w width face (channelSource (spectatorBlocks width face) q c) *
        sourceResponse w width face (channelSource (spectatorBlocks width face) q c)) ≈
      ((2*(1 + -(qpow w 12)))*(2*(1 + -(qpow w 12)))) *
        channelMeanSquares (N width) w K (spectatorBlocks width face)
          (polyMul q (characterPolynomial (plaquette width face).scalar 1)) := by
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let b := fun c => channelSource (spectatorBlocks width face) q c
  let f := characterPolynomial (plaquette width face).scalar 1
  let a := 2*(1 + -(qpow w 12))
  let M := fun c => H width (polyMul (b c) f) * H width (polyMul (b c) f)
  have hp : channelSum cs (fun c => sourceResponse w width face (b c) *
      sourceResponse w width face (b c)) ≈ channelSum cs (fun c => (a*a)*M c) :=
    sum_congr _ _ cs (fun c _ => response_square_pin w width face (b c.2))
  have hgram := channelMeanSquares_projected_pin (N width) w K
    (spectatorBlocks width face) (spectatorBlocks_lt width face) q f
    (plaquette_spectator_independent width face)
  exact Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ _ _ (sum_scale (a*a) M cs)
      (Q'.mul_eqv_congr_left _ _ _ hgram.symm))

/-- Retaining the complete spectator response family cannot weaken the old
single Haar-source response square. No interacting mean is substituted. -/
theorem channel_response_squares_ge_original {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width : Nat) (face : Z4Plaq) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    sourceResponse w width face q * sourceResponse w width face q ≤
      channelSum (productChannels (N width) w K (spectatorBlocks width face)) (fun c =>
        sourceResponse w width face (channelSource (spectatorBlocks width face) q c) *
          sourceResponse w width face (channelSource (spectatorBlocks width face) q c)) := by
  let f := characterPolynomial (plaquette width face).scalar 1
  let a := 2*(1 + -(qpow w 12))
  have hmean := channelMeanSquares_ge_haar_square (N width) hw0 K
    (spectatorBlocks width face)
    (List.filter_sublist.nodup (CayleyParentInj.range_nodup (N width)))
    (spectatorBlocks_lt width face) (polyMul q f)
    (supported_polyMul hq (character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (a*a) hmean
    (SumOfSquares.q_mul_self_nonneg a)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (response_square_pin w width face q))
    (Q'.le_trans' _ _ _ hs
      (Q'.ge_of_eqv (channel_response_squares_pin w K width face q)))

/-- The actual complete terminal source supplies both sides of the response
comparison. This statement needs no late-cutoff or stationarity premise. -/
theorem passive_responses_ge_original {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K width depth : Nat) (face : Z4Plaq) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    sourceResponse w width face q * sourceResponse w width face q ≤
      passiveResponseSquares w K width depth face := by
  dsimp only
  have hq : SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) := by
    unfold projectedEndpointSource
    exact familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  simpa only [passiveResponseSquares, plaquetteChannelSource] using
    channel_response_squares_ge_original hw0 K width face _ hq

/-- Two explicitly computed nonnegative corrections to the old original
Young ceiling: exact cost reduction and increase of retained response squares. -/
def passiveGain (w : Q') (K width depth : Nat) (face : Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  2*(plaquetteChannelCost width face w q-channelYoungCost width face w K q) +
    (passiveResponseSquares w K width depth face -
      sourceResponse w width face q * sourceResponse w width face q)

theorem passiveGain_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K width depth : Nat) (face : Z4Plaq) :
    (0 : Q') ≤ passiveGain w K width depth face := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  have hq : SupportedQuaternionBlocks (N width) q := by
    unfold q projectedEndpointSource
    exact familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width depth))
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.sub_nonneg_of_le (channelYoungCost_le_raw width face hw0 hw1 K q hq)))
    (Q'.sub_nonneg_of_le (passive_responses_ge_original hw0 K width depth face))

/-- The SAME original energy retains both gains. Positivity of either gain
and comparison with interacting variance remain analytic questions. -/
theorem padded_terminal_energy_with_passive_gain {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let f := characterPolynomial (plaquette width face).scalar 1
    4*energy w K width (terminalMessage w K width depth) f +
      sourceResponse w width face q * sourceResponse w width face q +
        passiveGain w K width depth face ≤ 2*plaquetteChannelCost width face w q := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := characterPolynomial (plaquette width face).scalar 1
  let E := energy w K width (terminalMessage w K width depth) f
  let J := sourceResponse w width face q
  let R := passiveResponseSquares w K width depth face
  let C := plaquetteChannelCost width face w q
  let Cc := channelYoungCost width face w K q
  have h := Q'.add_le_add_right _ _ (2*(C-Cc))
    (padded_terminal_passive_retained_square hw0 hw1 K hK2 hK hwidth depth face hf)
  have hl : 4*E+J*J+passiveGain w K width depth face ≈
      (4*E+R)+2*(C-Cc) := by
    unfold passiveGain
    exact poly_identity_of_normal_eq
      (.add (.add (.mul (.const 4) (.var 0)) (.mul (.var 1) (.var 1)))
        (.add (.mul (.const 2) (.add (.var 3) (.neg (.var 4))))
          (.add (.var 2) (.neg (.mul (.var 1) (.var 1))))))
      (.add (.add (.mul (.const 4) (.var 0)) (.var 2))
        (.mul (.const 2) (.add (.var 3) (.neg (.var 4)))))
      (by decide) (fun | 0 => E | 1 => J | 2 => R | 3 => C | _ => Cc)
  have hr : 2*Cc+2*(C-Cc) ≈ 2*C :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 1))
        (.mul (.const 2) (.add (.var 0) (.neg (.var 1)))))
      (.mul (.const 2) (.var 0)) (by decide) (fun | 0 => C | _ => Cc)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

#print axioms channel_response_squares_pin
#print axioms channel_response_squares_ge_original
#print axioms passive_responses_ge_original
#print axioms passiveGain_nonnegative
#print axioms padded_terminal_energy_with_passive_gain

end YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveResponseDominance
