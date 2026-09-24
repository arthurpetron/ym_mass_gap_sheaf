/-
# Spectator-channel contraction of the exact Taylor remainder

The kinetic pairing recombines EXACTLY. The conditional channel norm loss
is bounded by the passive angular cost with coefficient one, while the
remaining channel Casimir cost is bounded by the active angular cost.
Their sum proves contraction of the positive exact remainder form.

The conditional channel norm is NOT identified with the partial `productMap`,
which averages unselected coordinates. No original partition or variance
normalization is changed, and no scaling-uniform comparison is asserted.
-/

import YMGap.Continuum.SU2QuaternionFamilyChannelLoss
import YMGap.Continuum.SU2QuaternionExactRemainderForm

namespace YMGap.Continuum.SU2QuaternionRemainderChannelContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionExactRemainderForm
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

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

private theorem sum_neg (f : RatPoly → Q') (cs : List GramChannel) :
    channelSum cs (fun p => -(f p)) ≈ -(channelSum cs f) :=
  Q'.eqv_trans _ _ _ (sum_congr _ (fun p => (-1)*f p) cs (fun c _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
      (by decide) (fun _ => f c.2)))
    (Q'.eqv_trans _ _ _ (sum_scale (-1) f cs)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => channelSum cs f)))

private theorem moment_one (n : Nat) (w : Q') (K : Nat) (a : RatPoly) :
    sourceMoment n w K (List.range n) a polyOne ≈
      kineticPair n w K (List.range n) a a :=
  haar_of_coeff ((RatPolyCoeffEqv.mul_one a).mul_right _)

private theorem scalar_remainder_bound (P N Ns eps Cs A S : Q')
    (heps : (0 : Q') ≤ eps) (hloss : N-Ns ≤ eps*S) (hcost : Cs ≤ A) :
    P-Ns+eps*Cs ≤ P-N+eps*(S+A) := by
  have h := Q'.add_le_add_left (P-N) _ _
    (Q'.add_le_add hloss (Q'.mul_le_mul_of_nonneg_left _ _ _ hcost heps))
  have hleft : P-Ns+eps*Cs ≈ (P-N)+((N-Ns)+eps*Cs) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 2))) (.mul (.var 3) (.var 4)))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.add (.var 1) (.neg (.var 2))) (.mul (.var 3) (.var 4))))
      (by decide) (fun | 0 => P | 1 => N | 2 => Ns | 3 => eps | _ => Cs)
  have hright : (P-N)+(eps*S+eps*A) ≈ P-N+eps*(S+A) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

/-- The full spectator family contracts the exact positive Taylor remainder,
with coefficient one. This is a finite auxiliary seminorm statement, not an
interacting-variance or physical OS norm estimate. -/
theorem exactRemainderPair_channel_sum_le (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (active passive : List Nat)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1)))
    (hnd : passive.Nodup) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    channelSum (productChannels (tail+1) w K passive) (fun c =>
      exactRemainderPair tail w K (channelSource passive q c) (channelSource passive q c)) ≤
      exactRemainderPair tail w K q q := by
  let cs := productChannels (tail+1) w K passive
  let b := fun c => channelSource passive q c
  let P := kineticPair (tail+1) w K (List.range (tail+1)) q q
  let pn := fun c => kineticPair (tail+1) w K (List.range (tail+1)) (b c) (b c)
  let nn := fun c => H (tail+1) (polyMul (b c) (b c))
  let cc := fun c => pairCasimir tail (b c) (b c)
  let eps : Q' := 1-w
  have hp : P ≈ channelSum cs pn :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (moment_one (tail+1) w K q))
      (Q'.eqv_trans _ _ _
        (sourceMoment_projected_channels (tail+1) w K active passive hactive hpassive
          hnot hcover q polyOne hq (supported_one (tail+1))
          (fun i _ => quaternionBlockIndependent_polyOne i))
        (sum_congr _ _ cs (fun c _ => moment_one (tail+1) w K (b c.2))))
  have hr : channelSum cs (fun c => exactRemainderPair tail w K (b c) (b c)) ≈
      P-channelSum cs nn+eps*channelSum cs cc :=
    Q'.eqv_trans _ _ _ (sum_add (fun c => pn c+ -(nn c)) (fun c => eps*cc c) cs)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (sum_add pn (fun c => -(nn c)) cs)
            (Q'.add_eqv_congr' (Q'.eqv_symm hp) (sum_neg nn cs)))
          (sum_scale eps cc cs)) (Q'.eqv_refl _))
  have hloss := productChannels_familyProject_loss_le (tail+1) hw0 hw1 K hK
    passive hnd hpassive q hq
  have hcost := pairCasimir_channel_le_active (tail+1) (by omega)
    hw0 (Q'.le_of_lt hw1) K passive active hnd hpassive hactive
    (fun i hi hp => hnot i hp hi) hcover q hq
  have hsplit := pairCasimir_eq_angular_partition (tail+1) (by omega)
    passive active hcover q hq
  simp only [Nat.add_sub_cancel] at hcost hsplit
  have hbound := scalar_remainder_bound P (H (tail+1) (polyMul q q))
    (channelSum cs nn) eps (channelSum cs cc)
    (angularListSum (tail+1) active q) (angularListSum (tail+1) passive q)
    (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)) hloss hcost
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hr)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.mul_eqv_congr_left eps _ _ (Q'.eqv_symm hsplit)))))

private theorem remainder_diagonal_congr (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) (h : RatPolyCoeffEqv p q) :
    exactRemainderPair tail w K p p ≈ exactRemainderPair tail w K q q :=
  (exactRemainderGNSData tail w hw0 hw1 K hK).B_diag_congr
    (u := ⟨p, hp⟩) (v := ⟨q, hq⟩) h

/-- An insertion independent of every spectator passes through the actual
channel transform. Its exact remainder cost contracts with coefficient one. -/
theorem exactRemainderPair_weighted_channel_sum_le (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (active passive : List Nat)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1)))
    (hnd : passive.Nodup) (q r : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hr : SupportedQuaternionBlocks (tail+1) r)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i r) :
    channelSum (productChannels (tail+1) w K passive) (fun c =>
      exactRemainderPair tail w K (polyMul (channelSource passive q c) r)
        (polyMul (channelSource passive q c) r)) ≤
      exactRemainderPair tail w K (polyMul q r) (polyMul q r) := by
  let cs := productChannels (tail+1) w K passive
  have hpull (c : RatPoly) : RatPolyCoeffEqv
      (channelSource passive (polyMul q r) c)
      (polyMul (channelSource passive q c) r) :=
    (familyProject_congr passive (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => q | 1 => r | _ => c))).trans
      ((familyProject_mul_of_independent passive r (polyMul q c) hind).trans
        (RatPolyCoeffEqv.mul_comm _ _))
  have he : channelSum cs (fun c => exactRemainderPair tail w K
      (channelSource passive (polyMul q r) c) (channelSource passive (polyMul q r) c)) ≈
      channelSum cs (fun c => exactRemainderPair tail w K
        (polyMul (channelSource passive q c) r) (polyMul (channelSource passive q c) r)) :=
    sum_congr _ _ cs (fun c hc =>
      remainder_diagonal_congr tail hw0 hw1 K hK
        (familyProject_supported passive (supported_polyMul (supported_polyMul hq hr)
          (productChannels_supported (tail+1) w K passive hpassive c hc)))
        (supported_polyMul (familyProject_supported passive (supported_polyMul hq
          (productChannels_supported (tail+1) w K passive hpassive c hc))) hr)
        (hpull c.2))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (exactRemainderPair_channel_sum_le tail hw0 hw1 K hK active passive
      hactive hpassive hnot hcover hnd (polyMul q r) (supported_polyMul hq hr))

end YMGap.Continuum.SU2QuaternionRemainderChannelContraction

#print axioms YMGap.Continuum.SU2QuaternionRemainderChannelContraction.exactRemainderPair_channel_sum_le
#print axioms YMGap.Continuum.SU2QuaternionRemainderChannelContraction.exactRemainderPair_weighted_channel_sum_le
