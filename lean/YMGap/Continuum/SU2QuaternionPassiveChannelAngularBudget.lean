/-
# Coefficient-one angular cost for the complete spectator channel family

The actual heat-channel Bessel inequality is applied to each angular
derivative of the SAME observable. Spectator derivatives vanish; all other
derivatives retain spectator independence. Finite summation therefore costs
no channel-count or block-count factor.

The resulting source-energy bound still retains the complete mixed remainder
budget. Its raw source-square weight is NOT the interacting marginal or SAME
centered variance, and no changing-scale estimate is asserted.
-/

import YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
import YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction

namespace YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (clearQuaternionBlock)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionSelectedHaarDerivative
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem sum_congr (left right : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → left c.2 ≈ right c.2) → channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (sum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem sum_zero : ∀ cs : List GramChannel,
    channelSum cs (fun _ => 0) ≈ 0
  | [] => Q'.eqv_refl _
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_zero_eqv _) (sum_zero cs)) (by decide)

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
  | [] => (Q'.mul_zero_eqv a).symm
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => f c.2)) (sum_scale a f cs))
      (Q'.mul_add_eqv _ _ _).symm

private theorem sum_finSum (cs : List GramChannel) (f : RatPoly → Nat → Q') :
    ∀ m, channelSum cs (fun p => finSum (f p) m) ≈
      finSum (fun i => channelSum cs (fun p => f p i)) m
  | 0 => sum_zero cs
  | m+1 => Q'.eqv_trans _ _ _ (sum_add _ _ cs)
      (Q'.add_eqv_congr' (sum_finSum cs f m) (Q'.eqv_refl _))

private theorem sum_six (cs : List GramChannel) (f : RatPoly → Nat → Nat → Q') :
    channelSum cs (fun p => sixValue (f p)) ≈
      sixValue (fun i j => channelSum cs (fun p => f p i j)) := by
  have h (a b : RatPoly → Q') (v : Q') (hb : channelSum cs b ≈ v) :
      channelSum cs (fun p => a p+b p) ≈ channelSum cs a+v :=
    Q'.eqv_trans _ _ _ (sum_add a b cs) (Q'.add_eqv_congr' (Q'.eqv_refl _) hb)
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _ (sum_add _ _ cs))))

private theorem derivative_independent {selected block component : Nat}
    (hne : block ≠ selected) (hc : component < 4) {p : RatPoly}
    (hp : QuaternionBlockIndependent selected p) :
    QuaternionBlockIndependent selected (ratDerivative (4*block+component) p) := by
  intro term ht
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp ht
  change clearQuaternionBlock selected (lowerExponentAt (4*block+component) source.1) =
    lowerExponentAt (4*block+component) source.1
  rw [← lowerExponentAt_clearQuaternionBlock_of_ne hne hc, hp source hsource]

private theorem angular_independent {selected block i j : Nat}
    (hne : block ≠ selected) (hi : i < 4) (hj : j < 4) {p : RatPoly}
    (hp : QuaternionBlockIndependent selected p) :
    QuaternionBlockIndependent selected (blockAngularDerivative block i j p) := by
  exact quaternionBlockIndependent_polyAdd
    (quaternionBlockIndependent_polyMul
      (quaternionBlockIndependent_polyVar_of_distinctBlock hne hi)
      (derivative_independent hne hj hp))
    (quaternionBlockIndependent_polySmul (-1)
      (quaternionBlockIndependent_polyMul
        (quaternionBlockIndependent_polyVar_of_distinctBlock hne hj)
        (derivative_independent hne hi hp)))

private theorem derivative_cost_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (ids : List Nat) (hids : ∀ s, s ∈ ids → s < n) (hnd : ids.Nodup)
    (q f : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f)
    (hind : ∀ s, s ∈ ids → QuaternionBlockIndependent s f)
    (block i j : Nat) (hb : block < n) (hi : i < 4) (hj : j < 4) :
    channelSum (productChannels n w K ids) (fun c => H n
      (polyMul (polyMul (channelSource ids q c) (channelSource ids q c))
        (polyMul (blockAngularDerivative block i j f) (blockAngularDerivative block i j f)))) ≤
      H n (polyMul (polyMul q q)
        (polyMul (blockAngularDerivative block i j f) (blockAngularDerivative block i j f))) := by
  by_cases hm : block ∈ ids
  · have hz := angularDerivative_blockIndependent_zero hi hj (hind block hm)
    have hz' (a : RatPoly) : H n (polyMul (polyMul a a)
        (polyMul (blockAngularDerivative block i j f) (blockAngularDerivative block i j f))) ≈ 0 :=
      haar_of_coeff (((hz.mul hz).trans (RatPolyCoeffEqv.mul_zero_left _)).mul_left _ |>.trans
        (RatPolyCoeffEqv.mul_zero_right _))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (sum_congr _ (fun _ => 0) _ (fun c _ => hz' (channelSource ids q c.2)))
      (sum_zero _))) (Q'.ge_of_eqv (hz' q))
  · exact productChannels_familyProject_weighted_square_le n hw0 hw1 K ids hnd hids q
      (blockAngularDerivative block i j f) hq
      (angularDerivative_supported_at (by omega) (by omega) hf)
      (fun s hs => angular_independent (block := block) (selected := s)
        (fun he => hm (he.symm ▸ hs)) hi hj (hind s hs))

/-- The COMPLETE spectator-channel angular sum has coefficient one, not the
number of channels. The source square is raw Haar weight, not physical variance. -/
theorem channelSource_weightedAngularEnergy_le (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (ids : List Nat) (hids : ∀ s, s ∈ ids → s < tail+1) (hnd : ids.Nodup)
    (q f : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ s, s ∈ ids → QuaternionBlockIndependent s f) :
    channelSum (productChannels (tail+1) w K ids)
        (fun c => weightedAngularEnergy tail (channelSource ids q c) f) ≤
      weightedAngularEnergy tail q f := by
  let cs := productChannels (tail+1) w K ids
  let value := fun c block => H (tail+1)
    (polyMul (polyMul (channelSource ids q c) (channelSource ids q c))
      (blockAngularSquare block f))
  have hsum := sum_finSum cs value (tail+1)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum) ?_
  apply finSum_le_lt _ _ (tail+1)
  intro block hb
  let plane := fun c i j => H (tail+1)
    (polyMul (polyMul (channelSource ids q c) (channelSource ids q c))
      (polyMul (blockAngularDerivative block i j f) (blockAngularDerivative block i j f)))
  have hexpand : channelSum cs (fun c => value c block) ≈
      channelSum cs (fun c => sixValue (plane c)) :=
    sum_congr _ _ cs (fun c _ => haar_six (tail+1) _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    hexpand (sum_six cs plane)))
    (Q'.le_trans' _ _ _
      (sixValue_mono _ _ (fun i j hi hj =>
        derivative_cost_le (tail+1) hw0 hw1 K ids hids hnd q f hq hf hind block i j hb hi hj))
      (Q'.ge_of_eqv (haar_six (tail+1) (polyMul q q) _)))

/-- Actual source-energy consumer: only the mixed remainder retains a channel
sum. No sign, variance comparison or scaling bound on that remainder is assumed. -/
theorem sourceEnergy_le_angular_add_channel_mixed_budget (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (active passive : List Nat)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range (tail+1)))
    (hnd : passive.Nodup) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      ((1 : Q')-w)*weightedAngularEnergy tail a f +
        (((1 : Q')-w)*((1 : Q')-w)) *
          channelSum (productChannels (tail+1) w K passive) (fun c =>
            pairBudget tail (channelSource passive a c)
              (polyMul (channelSource passive a c) (polyMul f f))) := by
  have h := sourceEnergy_le_projected_channel_budgets tail hw0 hw1 K hK
    active passive hactive hpassive hnot hcover a f ha hf hind
  let cs := productChannels (tail+1) w K passive
  let angular := fun c => weightedAngularEnergy tail (channelSource passive a c) f
  let mixed := fun c => pairBudget tail (channelSource passive a c)
    (polyMul (channelSource passive a c) (polyMul f f))
  let eps : Q' := 1-w
  have he := Q'.eqv_trans _ _ _
    (sum_add (fun c => eps*angular c) (fun c => (eps*eps)*mixed c) cs)
    (Q'.add_eqv_congr' (sum_scale eps angular cs) (sum_scale (eps*eps) mixed cs))
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (channelSource_weightedAngularEnergy_le tail hw0 (Q'.le_of_lt hw1)
          K passive hpassive hnd a f ha hf hind)
        (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))) (Q'.le_refl' _)))

end YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget

#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget.channelSource_weightedAngularEnergy_le
#print axioms YMGap.Continuum.SU2QuaternionPassiveChannelAngularBudget.sourceEnergy_le_angular_add_channel_mixed_budget
