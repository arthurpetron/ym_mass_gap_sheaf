/-
# Factor-one loss for conditional product Gram channels

Unlike a selected `productMap`, this form leaves unselected coordinates in
place.  Its finite Cartesian channel expansion loses at most one copy of the
angular energy at each selected block.
-/

import YMGap.Continuum.SU2QuaternionSelectedHeatGramBessel
import YMGap.Continuum.SU2QuaternionChannelAngularContraction

namespace YMGap.Continuum.SU2QuaternionFamilyChannelLoss

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatGramLocality
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionSelectedHeatGramBessel
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation "H" => quaternionHaar
local infix:50 " ≈ " => Q'.eqv

/-- The conditional channel quadratic: only the listed blocks are projected. -/
def familyChannelQuadratic (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (p : RatPoly) : Q' :=
  channelSum (productChannels n w K ids) (fun h => H n
    (polyMul (familyProject ids (polyMul p h))
      (familyProject ids (polyMul p h))))

private theorem channelSum_append (value : RatPoly → Q') :
    ∀ left right : List GramChannel,
      channelSum (left ++ right) value ≈
        channelSum left value + channelSum right value
  | [], _ => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | _::cs, right => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_append value cs right))
      (Q'.add_assoc_eqv _ _ _).symm

private theorem channelSum_map_multiply (value : RatPoly → Q') (a : GramChannel) :
    ∀ bs : List GramChannel,
      channelSum (bs.map fun b => multiplyChannel a b) value ≈
        a.1 * channelSum bs (fun b => value (polyMul a.2 b))
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a.1)
  | b::bs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (channelSum_map_multiply value a bs))
      (poly_identity_of_normal_eq
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.var 0) (.var 3)))
        (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3)))
        (by decide)
        (fun | 0 => a.1 | 1 => b.1 | 2 => value (polyMul a.2 b.2)
             | _ => channelSum bs (fun d => value (polyMul a.2 d))))

private theorem channelSum_multiply (value : RatPoly → Q') :
    ∀ as bs : List GramChannel,
      channelSum (multiplyChannels as bs) value ≈
        channelSum as (fun a => channelSum bs (fun b => value (polyMul a b)))
  | [], _ => Q'.eqv_refl _
  | a::as, bs => Q'.eqv_trans _ _ _ (channelSum_append value _ _)
      (Q'.add_eqv_congr' (channelSum_map_multiply value a bs)
        (channelSum_multiply value as bs))

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left c.1 _ _ (h c List.mem_cons_self))
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

private theorem channelSum_sub (cs : List GramChannel) (left right : RatPoly → Q') :
    channelSum cs (fun p => left p - right p) ≈
      channelSum cs left - channelSum cs right := by
  induction cs with
  | nil => change (0 : Q') ≈ 0-0; decide
  | cons c cs ih =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (poly_identity_of_normal_eq
            (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
            (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
            (by decide) (fun | 0 => c.1 | 1 => left c.2 | _ => right c.2)) ih)
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.neg (.var 1)))
            (.add (.var 2) (.neg (.var 3))))
          (.add (.add (.var 0) (.var 2))
            (.neg (.add (.var 1) (.var 3))))
          (by decide)
          (fun | 0 => c.1*left c.2 | 1 => c.1*right c.2
               | 2 => channelSum cs left | _ => channelSum cs right))

private theorem channelSum_add (cs : List GramChannel) (left right : RatPoly → Q') :
    channelSum cs (fun p => left p + right p) ≈
      channelSum cs left + channelSum cs right := by
  induction cs with
  | nil => exact Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | cons c cs ih =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv c.1 (left c.2) (right c.2)) ih)
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
          (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
          (by decide)
          (fun | 0 => c.1*left c.2 | 1 => c.1*right c.2
               | 2 => channelSum cs left | _ => channelSum cs right))

private theorem channelSum_smul (cs : List GramChannel) (s : Q')
    (value : RatPoly → Q') :
    channelSum cs (fun p => s*value p) ≈ s*channelSum cs value := by
  induction cs with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv s)
  | cons c cs ih =>
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.var 3)))
          (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3)))
          (by decide)
          (fun | 0 => c.1 | 1 => s | 2 => value c.2
               | _ => channelSum cs value))

private theorem heatChannels_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (slot K : Nat) : ∀ c, c ∈ heatChannels slot w K → (0 : Q') ≤ c.1 := by
  intro c hc
  obtain ⟨degree, hd, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨k, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hc
  have hc0 : (0 : Q') ≤ coeffAt (heatKernelPacket K w) degree := by
    rw [coeffAt_heatKernelPacket (List.mem_range.mp hd)]
    exact coeffW_nonneg hw degree
  exact Q'.mul_nonneg _ _ hc0
    (Q'.le_of_lt (basisInverseWeight_pos degree k))

private theorem channelSum_zero : ∀ cs : List GramChannel,
    channelSum cs (fun _ => 0) ≈ 0
  | [] => Q'.eqv_refl _
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_zero_eqv c.1) (channelSum_zero cs))
      (QPoly.q_zero_add_eqv 0)

private theorem family_channel_project (i : Nat) (ids : List Nat)
    (q a b : RatPoly) (hb : QuaternionBlockIndependent i b) :
    RatPolyCoeffEqv
      (familyProject (i::ids) (polyMul q (polyMul a b)))
      (familyProject ids (polyMul (project i (polyMul q a)) b)) := by
  change RatPolyCoeffEqv
    (familyProject ids (project i (polyMul q (polyMul a b)))) _
  exact familyProject_congr ids
    ((project_congr i (RatPolyCoeffEqv.mul_assoc q a b).symm).trans
      (project_mul_right_of_independent i (polyMul q a) b hb))

private theorem square_haar_congr (n : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : H n (polyMul p p) ≈ H n (polyMul q q) :=
  haar_of_coeff (h.mul h)

private theorem oneLink_angularList_le (n slot : Nat) (hslot : slot < n)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (ids : List Nat) (hids : ∀ block, block ∈ ids → block < n)
    (hne : ∀ block, block ∈ ids → block ≠ slot)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    channelSum (heatChannels slot w K) (fun a =>
      angularListSum n ids (project slot (polyMul q a))) ≤
      angularListSum n ids q := by
  induction ids with
  | nil =>
      exact Q'.le_of_eqv (channelSum_zero (heatChannels slot w K))
  | cons block ids ih =>
      have hb := hids block List.mem_cons_self
      have hne' := hne block List.mem_cons_self
      have hhead := heatChannels_project_blockAngularSquare_le_at
        n slot hslot hw0 hw1 K block hb hne' q hq
      have htail := ih
        (fun j hj => hids j (List.mem_cons_of_mem block hj))
        (fun j hj => hne j (List.mem_cons_of_mem block hj))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (channelSum_add _ _ _))
        (Q'.add_le_add hhead htail)

/-- Factor-one angular loss for the conditional Cartesian channel family. -/
theorem productChannels_familyProject_loss_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) : ∀ (ids : List Nat),
    ids.Nodup → (∀ i, i ∈ ids → i < n) → (p : RatPoly) →
    SupportedQuaternionBlocks n p →
    H n (polyMul p p) - familyChannelQuadratic n w K ids p ≤
      ((1 : Q')-w)*angularListSum n ids p
  | [], _, _, p, _ => by
      have hv : H n (polyMul (polyMul p polyOne) (polyMul p polyOne)) ≈
          H n (polyMul p p) :=
        square_haar_congr n (RatPolyCoeffEqv.mul_one p)
      change H n (polyMul p p) -
        (1*H n (polyMul (polyMul p polyOne) (polyMul p polyOne)) + 0) ≤
          ((1 : Q')-w)*0
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left 1 _ _ hv) (Q'.eqv_refl _))))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.neg (.add (.mul (.const 1) (.var 0)) (.const 0))))
          (.mul (.var 1) (.const 0)) (by decide)
          (fun | 0 => H n (polyMul p p) | _ => (1 : Q')-w)))
  | i::ids, hnd, hids, p, hp => by
      have hi : i < n := hids i List.mem_cons_self
      have hnot : i ∉ ids := (List.nodup_cons.mp hnd).1
      have htnd := (List.nodup_cons.mp hnd).2
      have htids : ∀ j, j ∈ ids → j < n :=
        fun j hj => hids j (List.mem_cons_of_mem i hj)
      let N := fun q : RatPoly => H n (polyMul q q)
      let qa := fun a : RatPoly => project i (polyMul p a)
      let Q := fun q : RatPoly => familyChannelQuadratic n w K ids q
      let A := fun q : RatPoly => angularListSum n ids q
      have hflat : familyChannelQuadratic n w K (i::ids) p ≈
          channelSum (heatChannels i w K) (fun a => Q (qa a)) := by
        unfold familyChannelQuadratic
        exact Q'.eqv_trans _ _ _ (channelSum_multiply _ _ _)
          (channelSum_congr _ _ _ (fun a ha =>
            channelSum_congr _ _ _ (fun b hb => square_haar_congr n
              (family_channel_project i ids p a.2 b.2
                (productChannels_independent n w K ids i hnot b hb)))))
      have hpoint : ∀ a, a ∈ heatChannels i w K →
          N (qa a.2) - Q (qa a.2) ≤ ((1 : Q')-w)*A (qa a.2) := by
        intro a ha
        exact productChannels_familyProject_loss_le n hw0 hw1 K hK ids htnd htids
          (qa a.2) (project_supported i (supported_polyMul hp
            (heatChannels_supported hi w K a ha)))
      have hweighted := channelSum_le (fun a => N (qa a)-Q (qa a))
        (fun a => ((1 : Q')-w)*A (qa a)) (heatChannels i w K)
        (fun a ha => heatChannels_nonnegative hw0 i K a ha) hpoint
      have htailLoss : channelSum (heatChannels i w K) (fun a => N (qa a)) -
          channelSum (heatChannels i w K) (fun a => Q (qa a)) ≤
          ((1 : Q')-w)*channelSum (heatChannels i w K) (fun a => A (qa a)) :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm
          (channelSum_sub _ (fun a => N (qa a)) (fun a => Q (qa a)))))
          (Q'.le_trans' _ _ _ hweighted
            (Q'.le_of_eqv (channelSum_smul _ ((1 : Q')-w) (fun a => A (qa a)))))
      have hang : channelSum (heatChannels i w K) (fun a => A (qa a)) ≤ A p := by
        exact oneLink_angularList_le n i hi hw0 (Q'.le_of_lt hw1) K ids htids
          (fun j hj hji => hnot (hji ▸ hj)) p hp
      have htail := Q'.le_trans' _ _ _ htailLoss
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hang
          (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
      have hhead := heatChannels_project_square_loss_le_at
        n i hi hw0 hw1 K hK p hp
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hflat))
          (poly_identity_of_normal_eq
            (.add (.var 0) (.neg (.var 2)))
            (.add (.add (.var 0) (.neg (.var 1)))
              (.add (.var 1) (.neg (.var 2))))
            (by decide)
            (fun | 0 => N p
                 | 1 => channelSum (heatChannels i w K) (fun a => N (qa a))
                 | _ => channelSum (heatChannels i w K) (fun a => Q (qa a))))))
        (Q'.le_trans' _ _ _ (Q'.add_le_add hhead htail)
          (Q'.le_of_eqv (Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.mul_add_eqv ((1 : Q')-w)
              (H n (blockAngularSquare i p)) (A p)))
            (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_refl _)))))

end YMGap.Continuum.SU2QuaternionFamilyChannelLoss

#print axioms YMGap.Continuum.SU2QuaternionFamilyChannelLoss.familyChannelQuadratic
#print axioms YMGap.Continuum.SU2QuaternionFamilyChannelLoss.productChannels_familyProject_loss_le
