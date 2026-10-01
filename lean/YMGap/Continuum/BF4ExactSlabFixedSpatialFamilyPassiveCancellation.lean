/-
# Spectator cost contraction and retained responses for the WHOLE signed family

One common union of literal face supports determines the passive channels.
The complete original terminal source and all signed cross terms are retained.
The proved gain is nonnegative, not necessarily positive or variance-relative.
No physical scaling, nonzero limiting excitation or continuum gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyHeatEigen
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
import YMGap.Continuum.SU2QuaternionProductHeatPassiveYoungContraction
import YMGap.Continuum.SU2QuaternionProductHeatEigenResponse
import YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyPassiveCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceEnergy sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionProductHeatPassiveYoungContraction
open YMGap.Continuum.SU2QuaternionProductHeatEigenResponse
open YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource energy_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
  (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyHeatEigen (spatialSpan_fullRange)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported oddCentered_independent centered_source_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage

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

private theorem projected_supported (w : Q') (K width : Nat) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) :
    SupportedQuaternionBlocks (N width) (projectedEndpointSource w K width g) := by
  unfold projectedEndpointSource
  exact familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width) hg)

private theorem channel_supported (w : Q') (K width : Nat) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) (qs : List Z4Plaq)
    (c : GramChannel) (hc : c ∈ productChannels (N width) w K (familySpectatorBlocks width qs)) :
    SupportedQuaternionBlocks (N width)
      (channelSource (familySpectatorBlocks width qs) (projectedEndpointSource w K width g) c.2) :=
  familyProject_supported _ (supported_polyMul (projected_supported w K width g hg)
    (productChannels_supported (N width) w K (familySpectatorBlocks width qs)
      (familySpectatorBlocks_lt width qs) c hc))

/-- The exact channel cost on a COMMON footprint of the whole signed family. -/
def familyYoungCost (w : Q') (K width : Nat) (g : RatPoly)
    (coeff : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  channelSum (productChannels (N width) w K (familySpectatorBlocks width qs)) (fun c =>
    singleEndedCost (N width) w K (List.range (N width))
      (channelSource (familySpectatorBlocks width qs) (projectedEndpointSource w K width g) c)
      (spatialSpan width coeff qs))

/-- Retained channel responses of the complete source, not interacting means. -/
def familyResponseSquares (w : Q') (K width : Nat) (g : RatPoly)
    (coeff : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  channelSum (productChannels (N width) w K (familySpectatorBlocks width qs)) (fun c =>
    let b := channelSource (familySpectatorBlocks width qs) (projectedEndpointSource w K width g) c
    let r := eigenResponse (N width) (qpow w 12) b (spatialSpan width coeff qs)
    r*r)

/-- The generic cost contraction has its actual signed-family geometry and
complete interacting endpoint source supplied here. -/
theorem family_cost_le_original {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) (coeff : Z4Plaq → Q') (qs : List Z4Plaq) :
    familyYoungCost w K width g coeff qs ≤
      singleEndedCost (N width) w K (List.range (N width))
        (projectedEndpointSource w K width g) (spatialSpan width coeff qs) :=
  singleEndedCost_projected_channels_le (N width) hw0 hw1 K hK
    (familyObservableBlocks width qs) (familySpectatorBlocks width qs)
    (familySpectator_observable_cover width qs) _ _ (projected_supported w K width g hg)
    (spatialSpan_supported width coeff qs) (spatialSpan_familySpectator_independent width coeff qs)

/-- Preserve the actual original padded energy before estimating its cost. -/
theorem padded_family_energy_eq_channels (w : Q') (K : Nat)
    {base width : Nat} (hwidth : base < width) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    energy w K width g (spatialSpan width coeff qs) ≈
      channelSum (productChannels (N width) w K (familySpectatorBlocks width qs)) (fun c =>
        sourceEnergy (N width) w K (List.range (N width))
          (channelSource (familySpectatorBlocks width qs) (projectedEndpointSource w K width g) c)
          (spatialSpan width coeff qs)) :=
  Q'.eqv_trans _ _ _
    (energy_projected_source w K width g _ hg (spatialSpan_supported width coeff qs)
      (spatialSpan_fringe_independent_after_padding hwidth coeff qs hqs))
    (sourceEnergy_projected_channels (N width) w K
      (familyObservableBlocks width qs) (familySpectatorBlocks width qs)
      (familyObservableBlocks_lt width qs) (familySpectatorBlocks_lt width qs)
      (familySpectator_not_observable width qs) (familySpectator_observable_cover width qs)
      _ _ (projected_supported w K width g hg) (spatialSpan_supported width coeff qs)
      (spatialSpan_familySpectator_independent width coeff qs))

/-- The whole signed observable supplies its own heat eigenpin, so its
responses are retained without an additional analytic input. -/
theorem padded_family_energy_channel_responses {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK1 : 1 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    4*energy w K width g (spatialSpan width coeff qs) +
      familyResponseSquares w K width g coeff qs ≤ 2*familyYoungCost w K width g coeff qs := by
  let f := spatialSpan width coeff qs
  let cs := productChannels (N width) w K (familySpectatorBlocks width qs)
  let b := fun c => channelSource (familySpectatorBlocks width qs) (projectedEndpointSource w K width g) c
  let E := fun c => sourceEnergy (N width) w K (List.range (N width)) (b c) f
  let C := fun c => singleEndedCost (N width) w K (List.range (N width)) (b c) f
  let R := fun c => eigenResponse (N width) (qpow w 12) (b c) f *
    eigenResponse (N width) (qpow w 12) (b c) f
  have heig := spatialSpan_fullRange width coeff qs
    (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp)) w K hK1
  have hpoint : channelSum cs (fun c => 4*E c+R c) ≤ channelSum cs (fun c => 2*C c) := by
    apply sum_le
    · exact productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K _
    · intro c hc
      have hb := channel_supported w K width g hg qs c hc
      have hlow := sourceIncrement_ge_eigenResponse_square (N width) hw0 hw1 K hK
        (List.range (N width)) (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi)
        hb (spatialSpan_supported width coeff qs) (qpow w 12) heig
      exact Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hlow)
        (Q'.le_of_eqv (four_mul_sourceEnergy_add_increment_eq_two_singleEnded
          (N width) w K (List.range (N width)) (fun _ hi => List.mem_range.mp hi)
          hb (spatialSpan_supported width coeff qs)))
  have hE := padded_family_energy_eq_channels w K hwidth g hg coeff qs hqs
  have hl := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left 4 _ _ hE))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (sum_scale 4 E cs).symm)
      (sum_add (fun c => 4*E c) R cs).symm)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hpoint (Q'.le_of_eqv (sum_scale 2 C cs)))

private theorem response_square_pin (n : Nat) (lambda : Q') (q f : RatPoly) :
    eigenResponse n lambda q f * eigenResponse n lambda q f ≈
      ((2*(1 + -lambda))*(2*(1 + -lambda))) *
        (quaternionHaar n (polyMul q f) * quaternionHaar n (polyMul q f)) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.const 2) (.mul (.var 0) (.var 1)))
      (.mul (.const 2) (.mul (.var 0) (.var 1))))
    (.mul (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
      (.mul (.var 1) (.var 1))) (by decide)
    (fun | 0 => 1 + -lambda | _ => quaternionHaar n (polyMul q f))

/-- Retaining all common spectator response squares dominates the original
whole-family response square; none is relabeled an interacting mean. -/
theorem family_responses_ge_original {w : Q'} (hw0 : (0 : Q') ≤ w) (K width : Nat)
    (g : RatPoly) (hg : SupportedQuaternionBlocks (N width) g)
    (coeff : Z4Plaq → Q') (qs : List Z4Plaq) :
    let q := projectedEndpointSource w K width g
    let f := spatialSpan width coeff qs
    eigenResponse (N width) (qpow w 12) q f * eigenResponse (N width) (qpow w 12) q f ≤
      familyResponseSquares w K width g coeff qs := by
  dsimp only
  let q := projectedEndpointSource w K width g
  let f := spatialSpan width coeff qs
  let cs := productChannels (N width) w K (familySpectatorBlocks width qs)
  let b := fun c => channelSource (familySpectatorBlocks width qs) q c
  let a := 2*(1 + -(qpow w 12))
  let M := fun c => H width (polyMul (b c) f) * H width (polyMul (b c) f)
  have hp : familyResponseSquares w K width g coeff qs ≈
      channelSum cs (fun c => (a*a)*M c) :=
    sum_congr
      (fun c => eigenResponse (N width) (qpow w 12) (b c) f *
        eigenResponse (N width) (qpow w 12) (b c) f)
      (fun c => (a*a)*M c) cs
      (fun c _ => response_square_pin (N width) (qpow w 12) (b c.2) f)
  have hsum : familyResponseSquares w K width g coeff qs ≈
      (a*a)*channelMeanSquares (N width) w K (familySpectatorBlocks width qs) (polyMul q f) :=
    Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (sum_scale (a*a) M cs)
        (Q'.mul_eqv_congr_left _ _ _
          (channelMeanSquares_projected_pin (N width) w K (familySpectatorBlocks width qs)
            (familySpectatorBlocks_lt width qs) q f
            (spatialSpan_familySpectator_independent width coeff qs)).symm))
  have hmean := channelMeanSquares_ge_haar_square (N width) hw0 K
    (familySpectatorBlocks width qs) (familySpectatorBlocks_nodup width qs)
    (familySpectatorBlocks_lt width qs) (polyMul q f)
    (supported_polyMul (projected_supported w K width g hg) (spatialSpan_supported width coeff qs))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (a*a) hmean (SumOfSquares.q_mul_self_nonneg a)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (response_square_pin (N width) (qpow w 12) q f))
    (Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv hsum))

/-- Both retained gains for the SAME original whole-family cost. -/
def familyGain (w : Q') (K width : Nat) (g : RatPoly)
    (coeff : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let q := projectedEndpointSource w K width g
  let f := spatialSpan width coeff qs
  let r := eigenResponse (N width) (qpow w 12) q f
  2*(singleEndedCost (N width) w K (List.range (N width)) q f-familyYoungCost w K width g coeff qs) +
    (familyResponseSquares w K width g coeff qs-r*r)

theorem familyGain_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) (coeff : Z4Plaq → Q') (qs : List Z4Plaq) :
    (0 : Q') ≤ familyGain w K width g coeff qs :=
  Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.sub_nonneg_of_le (family_cost_le_original hw0 hw1 K width hK g hg coeff qs)))
    (Q'.sub_nonneg_of_le (family_responses_ge_original (Q'.le_of_lt hw0) K width g hg coeff qs))

/-- The complete original terminal source supplies the whole signed-family
ceiling. No useful gain relative to interacting variance is presumed. -/
theorem padded_terminal_family_energy_with_gain {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK1 : 1 ≤ K) (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (depth : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let q := projectedEndpointSource w K width g
    let f := spatialSpan width coeff qs
    let r := eigenResponse (N width) (qpow w 12) q f
    4*energy w K width g f+r*r+familyGain w K width g coeff qs ≤
      2*singleEndedCost (N width) w K (List.range (N width)) q f := by
  dsimp only
  let g := terminalMessage w K width depth
  let q := projectedEndpointSource w K width g
  let f := spatialSpan width coeff qs
  let E := energy w K width g f
  let J := eigenResponse (N width) (qpow w 12) q f
  let R := familyResponseSquares w K width g coeff qs
  let C := singleEndedCost (N width) w K (List.range (N width)) q f
  let Cc := familyYoungCost w K width g coeff qs
  have h := Q'.add_le_add_right _ _ (2*(C-Cc))
    (padded_family_energy_channel_responses hw0 hw1 K hK1 hK hwidth g
      (terminalMessage_supported w K width depth) coeff qs hqs)
  have hl : 4*E+J*J+familyGain w K width g coeff qs ≈ (4*E+R)+2*(C-Cc) := by
    unfold familyGain
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

/-- The SAME globally centered variance is exactly the sum of original
channel moments. These individual terms are NOT asserted nonnegative, nor
are they separate probability measures or channel-centered variances. -/
theorem padded_family_centered_channel_variance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (depth : Nat) (coeff : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let f := spatialSpan width coeff qs
    let psi := oddCentered hw0 hw1 K width hK depth f
    channelSum (productChannels (N width) w K (familySpectatorBlocks width qs)) (fun c =>
      sourceMoment (N width) w K (List.range (N width))
        (channelSource (familySpectatorBlocks width qs) q c) (polyMul psi psi)) ≈
      oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f := by
  dsimp only
  let f := spatialSpan width coeff qs
  let psi := oddCentered hw0 hw1 K width hK depth f
  have hp := oddCentered_supported hw0 hw1 K width hK depth (spatialSpan_supported width coeff qs)
  have hi : ∀ i, i ∈ familySpectatorBlocks width qs → QuaternionBlockIndependent i psi :=
    fun i hi => oddCentered_independent hw0 hw1 K width hK depth i
      (spatialSpan_familySpectator_independent width coeff qs i hi)
  have hchannels := sourceMoment_projected_channels (N width) w K
    (familyObservableBlocks width qs) (familySpectatorBlocks width qs)
    (familyObservableBlocks_lt width qs) (familySpectatorBlocks_lt width qs)
    (familySpectator_not_observable width qs) (familySpectator_observable_cover width qs)
    (projectedEndpointSource w K width (terminalMessage w K width depth)) (polyMul psi psi)
    (projected_supported w K width _ (terminalMessage_supported w K width depth))
    (supported_polyMul hp hp)
    (fun i hs => quaternionBlockIndependent_polyMul (hi i hs) (hi i hs))
  exact Q'.eqv_trans _ _ _ hchannels.symm
    (centered_source_square hw0 hw1 K width hK depth (spatialSpan_supported width coeff qs)
      (spatialSpan_fringe_independent_after_padding hwidth coeff qs hqs))

#print axioms family_cost_le_original
#print axioms padded_family_energy_eq_channels
#print axioms padded_family_energy_channel_responses
#print axioms family_responses_ge_original
#print axioms familyGain_nonnegative
#print axioms padded_terminal_family_energy_with_gain
#print axioms padded_family_centered_channel_variance

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyPassiveCancellation
