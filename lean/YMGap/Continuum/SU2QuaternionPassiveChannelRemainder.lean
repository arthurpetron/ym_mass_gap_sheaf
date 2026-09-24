/-
# Signed remainder squares in the ORIGINAL spectator-channel energy

Polarization is performed before taking any absolute values. The exact
channel identity retains both negative remainder squares. Only the first-order
angular term is contracted by the proved coefficient-one family estimate.

No channelwise probability normalization is used. The remaining signed sum
is not bounded here against the original centered variance or across scales.
-/

import YMGap.Continuum.SU2QuaternionExactRemainderEnergy
import YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget

namespace YMGap.Continuum.SU2QuaternionPassiveChannelRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget
open YMGap.Continuum.SU2QuaternionExactRemainderEnergy
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv

private theorem sum_congr (left right : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → left c.2 ≈ right c.2) → channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (sum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem sum_add (f g : RatPoly → Q') : ∀ cs : List GramChannel,
    channelSum cs (fun p => f p+g p) ≈ channelSum cs f+channelSum cs g
  | [] => by change (0 : Q') ≈ 0+0; decide
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (sum_add f g cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
        (fun | 0 => c.1*f c.2 | 1 => c.1*g c.2
             | 2 => channelSum cs f | _ => channelSum cs g))

private theorem sum_scale (a : Q') (f : RatPoly → Q') : ∀ cs : List GramChannel,
    channelSum cs (fun p => a*f p) ≈ a*channelSum cs f
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => f c.2)) (sum_scale a f cs))
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

private theorem sum_le (left right : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
    (∀ c, c ∈ cs → left c.2 ≤ right c.2) → channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (h c List.mem_cons_self) (hw c List.mem_cons_self))
      (sum_le left right cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

/-- Exact channel recombination of the polarized source energy. All signed
diagonal terms remain in `polarizedRemainder`; no estimate has been taken. -/
theorem sourceEnergy_eq_polarized_channels (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (active passive : List Nat)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1)))
    (s : Q') (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    (2*s)*sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≈
      ((2*s)*((1 : Q')-w))*
        channelSum (productChannels (tail+1) w K passive)
          (fun c => weightedAngularEnergy tail (channelSource passive a c) f) +
      channelSum (productChannels (tail+1) w K passive)
        (fun c => polarizedRemainder tail w K s (channelSource passive a c) f) := by
  let cs := productChannels (tail+1) w K passive
  let e := fun c => sourceEnergy (tail+1) w K (List.range (tail+1))
    (channelSource passive a c) f
  let angular := fun c => weightedAngularEnergy tail (channelSource passive a c) f
  let rest := fun c => polarizedRemainder tail w K s (channelSource passive a c) f
  let factor : Q' := (2*s)*((1 : Q')-w)
  have henergy := Q'.mul_eqv_congr_left (2*s) _ _
    (sourceEnergy_projected_channels (tail+1) w K active passive hactive hpassive
      hnot hcover a f ha hf hind)
  have hchannel : channelSum cs (fun c => (2*s)*e c) ≈
      channelSum cs (fun c => factor*angular c+rest c) :=
    sum_congr _ _ cs (fun c hc =>
      sourceEnergy_polarized_remainder tail w hw0 hw1 K hK s
        (channelSource passive a c.2) f
        (familyProject_supported passive (supported_polyMul ha
          (productChannels_supported (tail+1) w K passive hpassive c hc))) hf)
  exact Q'.eqv_trans _ _ _ henergy
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (sum_scale (2*s) e cs))
      (Q'.eqv_trans _ _ _ hchannel
        (Q'.eqv_trans _ _ _ (sum_add (fun c => factor*angular c) rest cs)
          (Q'.add_eqv_congr' (sum_scale factor angular cs) (Q'.eqv_refl _)))))

/-- Coefficient-one angular contraction with ALL signed remainder squares
retained. No absolute mode-tree budget or channel-count factor is introduced. -/
theorem sourceEnergy_le_angular_add_polarized_channels (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (active passive : List Nat)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1)))
    (hnd : passive.Nodup) (s : Q') (hs : (0 : Q') ≤ s) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    (2*s)*sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      (2*s)*((1 : Q')-w)*weightedAngularEnergy tail a f +
        channelSum (productChannels (tail+1) w K passive)
          (fun c => polarizedRemainder tail w K s (channelSource passive a c) f) := by
  have h := sourceEnergy_eq_polarized_channels tail hw0 hw1 K hK active passive
    hactive hpassive hnot hcover s a f ha hf hind
  have hfactor : (0 : Q') ≤ (2*s)*((1 : Q')-w) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hs)
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (channelSource_weightedAngularEnergy_le tail hw0 (Q'.le_of_lt hw1)
          K passive hpassive hnd a f ha hf hind) hfactor)
      (Q'.le_refl' _))

/-- Positive remainder-form estimate on the complete channel sum. Only the
balancing residual square is dropped; the negative `R(a*f,a*f)` term remains. -/
theorem sourceEnergy_le_angular_add_balanced_channels (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (active passive : List Nat)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1)))
    (hnd : passive.Nodup) (s : Q') (hs : (0 : Q') ≤ s) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    (2*s)*sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      (2*s)*((1 : Q')-w)*weightedAngularEnergy tail a f +
        channelSum (productChannels (tail+1) w K passive)
          (fun c => balancedRemainder tail w K s (channelSource passive a c) f) :=
  Q'.le_trans' _ _ _
    (sourceEnergy_le_angular_add_polarized_channels tail hw0 hw1 K hK active passive
      hactive hpassive hnot hcover hnd s hs a f ha hf hind)
    (Q'.add_le_add (Q'.le_refl' _)
      (sum_le _ _ _ (productChannels_nonnegative (tail+1) hw0 K passive)
        (fun c hc => polarizedRemainder_le_balancedRemainder tail w hw0 hw1 K hK s
          (channelSource passive a c.2) f
          (familyProject_supported passive (supported_polyMul ha
            (productChannels_supported (tail+1) w K passive hpassive c hc))) hf)))

end YMGap.Continuum.SU2QuaternionPassiveChannelRemainder

#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelRemainder.sourceEnergy_eq_polarized_channels
#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelRemainder.sourceEnergy_le_angular_add_polarized_channels
#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelRemainder.sourceEnergy_le_angular_add_balanced_channels
