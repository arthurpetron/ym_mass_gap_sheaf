/-
# Passive-channel remainder control by the original active Casimir square

The exact diagonal remainder is first bounded by the computed cyclic-sweep
square.  The complete spectator channel family then contracts that square to
the original active-only second-derivative norm, with no channel-count loss.
-/

import YMGap.Continuum.SU2QuaternionCyclicCasimirSquare
import YMGap.Continuum.SU2QuaternionPassiveChannelCasimirSquare
import YMGap.Continuum.SU2QuaternionPassiveChannelRemainder

namespace YMGap.Continuum.SU2QuaternionPassiveChannelRemainderSobolev

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCasimirSweep
open YMGap.Continuum.SU2QuaternionCyclicCasimirSquare
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionExactRemainderEnergy
open YMGap.Continuum.SU2QuaternionExactRemainderForm
open YMGap.Continuum.SU2QuaternionPassiveChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionPassiveChannelRemainder
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem channelSum_le (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → left c.2 ≤ right c.2) →
      channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (h c List.mem_cons_self) (hw c List.mem_cons_self))
      (channelSum_le left right cs
        (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_scale (a : Q') (f : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun p => a*f p) ≈ a*channelSum cs f
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => f c.2))
        (channelSum_scale a f cs))
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_add (f g : RatPoly → Q') : ∀ cs : List GramChannel,
    channelSum cs (fun p => f p+g p) ≈ channelSum cs f+channelSum cs g
  | [] => by change (0 : Q') ≈ 0+0; decide
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (channelSum_add f g cs))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
          (.add (.var 3) (.var 4)))
        (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
          (.add (.mul (.var 0) (.var 2)) (.var 4))) (by decide)
        (fun | 0 => c.1 | 1 => f c.2 | 2 => g c.2
             | 3 => channelSum cs f | _ => channelSum cs g))

private theorem channelSum_neg (f : RatPoly → Q') (cs : List GramChannel) :
    channelSum cs (fun p => -(f p)) ≈ -(channelSum cs f) :=
  Q'.eqv_trans _ _ _ (channelSum_congr _ (fun p => (-1)*f p) cs (fun c _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
      (by decide) (fun _ => f c.2)))
    (Q'.eqv_trans _ _ _ (channelSum_scale (-1) f cs)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => channelSum cs f)))

/-- The complete passive-channel sum of exact diagonal remainders is bounded
by `(1-w)^2` times the ORIGINAL active Casimir square. -/
theorem exactRemainderPair_channel_sum_le_activeCasimir_square
    (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K)
    (passive active : List Nat)
    (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive ++ active).Perm (List.range (tail+1)))
    (q : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q) :
    channelSum (productChannels (tail+1) w K passive) (fun c =>
      exactRemainderPair tail w K (channelSource passive q c)
        (channelSource passive q c)) ≤
      (((1 : Q')-w)*((1 : Q')-w))*
        H (tail+1) (polyMul (activeCasimirPolynomial active q)
          (activeCasimirPolynomial active q)) := by
  let cs := productChannels (tail+1) w K passive
  let eps2 := ((1 : Q')-w)*((1 : Q')-w)
  let sweepSq := fun p : RatPoly => H (tail+1) (polyMul
    (casimirSweep tail (tail+1) p) (casimirSweep tail (tail+1) p))
  let sourceSweep := fun c : RatPoly => sweepSq (channelSource passive q c)
  have hsource (c : GramChannel) (hc : c ∈ cs) :
      SupportedQuaternionBlocks (tail+1) (channelSource passive q c.2) :=
    familyProject_supported passive (supported_polyMul hq
      (productChannels_supported (tail+1) w K passive hpassive c hc))
  have hraw : channelSum cs (fun c => exactRemainderPair tail w K
      (channelSource passive q c) (channelSource passive q c)) ≤
      channelSum cs (fun c => eps2*sourceSweep c) :=
    channelSum_le _ _ cs (productChannels_nonnegative (tail+1) hw0 K passive)
      (fun c hc => exactRemainderPair_diagonal_le_sweepSquare tail hw0 hw1 K hK
        (channelSource passive q c.2) (hsource c hc))
  have heps : (0 : Q') ≤ eps2 := Q'.mul_nonneg _ _
    (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
    (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (channelSum_scale eps2 sourceSweep cs))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (channelSource_casimirSweep_square_le tail hw0 (Q'.le_of_lt hw1) K
          passive active hnd hpassive hactive hnot hcover q hq) heps))

/-- A passive-independent insertion remains inside every exact channel
remainder, and the right side is the original active Casimir square of `q*r`. -/
theorem exactRemainderPair_mul_channel_sum_le_activeCasimir_square
    (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K)
    (passive active : List Nat)
    (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive ++ active).Perm (List.range (tail+1)))
    (q r : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hr : SupportedQuaternionBlocks (tail+1) r)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i r) :
    channelSum (productChannels (tail+1) w K passive) (fun c =>
      exactRemainderPair tail w K (polyMul (channelSource passive q c) r)
        (polyMul (channelSource passive q c) r)) ≤
      (((1 : Q')-w)*((1 : Q')-w))*
        H (tail+1) (polyMul
          (activeCasimirPolynomial active (polyMul q r))
          (activeCasimirPolynomial active (polyMul q r))) := by
  let cs := productChannels (tail+1) w K passive
  let eps2 := ((1 : Q')-w)*((1 : Q')-w)
  let sweepSq := fun p : RatPoly => H (tail+1) (polyMul
    (casimirSweep tail (tail+1) p) (casimirSweep tail (tail+1) p))
  let insertedSweep := fun c : RatPoly =>
    sweepSq (polyMul (channelSource passive q c) r)
  have hsource (c : GramChannel) (hc : c ∈ cs) :
      SupportedQuaternionBlocks (tail+1) (polyMul (channelSource passive q c.2) r) :=
    supported_polyMul
      (familyProject_supported passive (supported_polyMul hq
        (productChannels_supported (tail+1) w K passive hpassive c hc))) hr
  have hraw : channelSum cs (fun c => exactRemainderPair tail w K
      (polyMul (channelSource passive q c) r)
      (polyMul (channelSource passive q c) r)) ≤
      channelSum cs (fun c => eps2*insertedSweep c) :=
    channelSum_le _ _ cs (productChannels_nonnegative (tail+1) hw0 K passive)
      (fun c hc => exactRemainderPair_diagonal_le_sweepSquare tail hw0 hw1 K hK
        (polyMul (channelSource passive q c.2) r) (hsource c hc))
  have heps : (0 : Q') ≤ eps2 := Q'.mul_nonneg _ _
    (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
    (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (channelSum_scale eps2 insertedSweep cs))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (channelSource_mul_casimirSweep_square_le tail hw0 (Q'.le_of_lt hw1) K
          passive active hnd hpassive hactive hnot hcover q r hq hr hind) heps))

/-- The actual source energy has an active-only second-derivative budget for
its two positive diagonal remainder sums.  The favorable negative channel
sum is retained verbatim; no comparison with interacting variance is made. -/
theorem sourceEnergy_le_angular_add_activeCasimir_diagonals
    (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K)
    (active passive : List Nat)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive ++ active).Perm (List.range (tail+1)))
    (hnd : passive.Nodup) (s : Q') (hs : (0 : Q') ≤ s)
    (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    (2*s)*sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      (2*s)*((1 : Q')-w)*weightedAngularEnergy tail a f +
        ((s*s)*((((1 : Q')-w)*((1 : Q')-w))*
          H (tail+1) (polyMul (activeCasimirPolynomial active a)
            (activeCasimirPolynomial active a))) +
        (((1 : Q')-w)*((1 : Q')-w))*
          H (tail+1) (polyMul
            (activeCasimirPolynomial active (polyMul a (polyMul f f)))
            (activeCasimirPolynomial active (polyMul a (polyMul f f)))) +
        -((2*s)*channelSum (productChannels (tail+1) w K passive) (fun c =>
          exactRemainderPair tail w K (polyMul (channelSource passive a c) f)
            (polyMul (channelSource passive a c) f)))) := by
  let cs := productChannels (tail+1) w K passive
  let b := fun c => channelSource passive a c
  let ra := fun c => exactRemainderPair tail w K (b c) (b c)
  let ry := fun c => exactRemainderPair tail w K
    (polyMul (b c) (polyMul f f)) (polyMul (b c) (polyMul f f))
  let rz := fun c => exactRemainderPair tail w K
    (polyMul (b c) f) (polyMul (b c) f)
  have hsum : channelSum cs (fun c => balancedRemainder tail w K s (b c) f) ≈
      (s*s)*channelSum cs ra+channelSum cs ry + -((2*s)*channelSum cs rz) :=
    Q'.eqv_trans _ _ _
      (channelSum_add (fun c => (s*s)*ra c+ry c) (fun c => -((2*s)*rz c)) cs)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (channelSum_add (fun c => (s*s)*ra c) ry cs)
          (Q'.add_eqv_congr' (channelSum_scale (s*s) ra cs) (Q'.eqv_refl _)))
        (Q'.eqv_trans _ _ _ (channelSum_neg (fun c => (2*s)*rz c) cs)
          (Q'.neg_eqv_congr _ _ (channelSum_scale (2*s) rz cs))))
  have hbase := sourceEnergy_le_angular_add_balanced_channels tail hw0 hw1 K hK
    active passive hactive hpassive hnot hcover hnd s hs a f ha hf hind
  have hra := exactRemainderPair_channel_sum_le_activeCasimir_square tail hw0 hw1 K
    hK passive active hnd hpassive hactive hnot hcover a ha
  have hry := exactRemainderPair_mul_channel_sum_le_activeCasimir_square tail hw0 hw1 K
    hK passive active hnd hpassive hactive hnot hcover a (polyMul f f) ha
    (supported_polyMul hf hf)
    (fun i hi => quaternionBlockIndependent_polyMul (hind i hi) (hind i hi))
  exact Q'.le_trans' _ _ _ hbase
    (Q'.add_le_add (Q'.le_refl' _)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
        (Q'.add_le_add
          (Q'.add_le_add
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hra
              (Q'.mul_nonneg _ _ hs hs)) hry)
          (Q'.le_refl' _))))

end YMGap.Continuum.SU2QuaternionPassiveChannelRemainderSobolev

#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelRemainderSobolev.exactRemainderPair_channel_sum_le_activeCasimir_square
#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelRemainderSobolev.exactRemainderPair_mul_channel_sum_le_activeCasimir_square
#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelRemainderSobolev.sourceEnergy_le_angular_add_activeCasimir_diagonals
