/-
# Coefficient-one Bessel contraction for a finite selected heat family

The literal Cartesian Gram channels are summed one selected block at a time.
Distinctness is used only to pull the remaining channel polynomial through the
current in-place Haar projection.  The sole analytic input at each step is the
already-proved selected one-link channel Bessel inequality.
-/

import YMGap.Continuum.SU2QuaternionSelectedHeatGramBessel
import YMGap.Continuum.SU2QuaternionProductHeatGramLocality
import YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels

namespace YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatGramLocality
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionSelectedHeatGramBessel

local notation "H" => quaternionHaar
local infix:50 " ≈ " => Q'.eqv

private theorem channelSum_append (value : RatPoly → Q') :
    ∀ left right : List GramChannel,
      channelSum (left ++ right) value ≈
        channelSum left value + channelSum right value
  | [], right => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | c :: cs, right => by
      change c.1 * value c.2 + channelSum (cs ++ right) value ≈
        (c.1 * value c.2 + channelSum cs value) + channelSum right value
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (channelSum_append value cs right)) (poly_identity_of_normal_eq
          (.add (.var 0) (.add (.var 1) (.var 2)))
          (.add (.add (.var 0) (.var 1)) (.var 2)) (by decide)
          (fun | 0 => c.1 * value c.2 | 1 => channelSum cs value
               | _ => channelSum right value))

private theorem channelSum_map_multiply (value : RatPoly → Q') (a : GramChannel) :
    ∀ bs : List GramChannel,
      channelSum (bs.map fun b => multiplyChannel a b) value ≈
        a.1 * channelSum bs (fun b => value (polyMul a.2 b))
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a.1)
  | b :: bs => by
      change (a.1*b.1)*value (polyMul a.2 b.2) +
          channelSum (bs.map fun d => multiplyChannel a d) value ≈
        a.1*(b.1*value (polyMul a.2 b.2) +
          channelSum bs (fun d => value (polyMul a.2 d)))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
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
        channelSum as (fun a => channelSum bs
          (fun b => value (polyMul a b)))
  | [], bs => Q'.eqv_refl _
  | a :: as, bs => by
      change channelSum ((bs.map fun b => multiplyChannel a b) ++
          multiplyChannels as bs) value ≈
        a.1 * channelSum bs (fun b => value (polyMul a.2 b)) +
          channelSum as (fun c => channelSum bs (fun b => value (polyMul c b)))
      exact Q'.eqv_trans _ _ _ (channelSum_append value _ _)
        (Q'.add_eqv_congr' (channelSum_map_multiply value a bs)
          (channelSum_multiply value as bs))

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c :: cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left c.1 _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_le (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → left c.2 ≤ right c.2) →
      channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c :: cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (h c List.mem_cons_self)
        (hw c List.mem_cons_self))
      (channelSum_le left right cs
        (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

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

private theorem family_channel_project (i : Nat) (ids : List Nat)
    (q a b : RatPoly) (hb : QuaternionBlockIndependent i b) :
    RatPolyCoeffEqv
      (familyProject (i :: ids) (polyMul q (polyMul a b)))
      (familyProject ids (polyMul (project i (polyMul q a)) b)) := by
  change RatPolyCoeffEqv
    (familyProject ids (project i (polyMul q (polyMul a b)))) _
  have hassoc : RatPolyCoeffEqv (polyMul q (polyMul a b))
      (polyMul (polyMul q a) b) := RatPolyCoeffEqv.mul_assoc _ _ _ |>.symm
  exact familyProject_congr ids
    (RatPolyCoeffEqv.trans (project_congr i hassoc)
      (project_mul_right_of_independent i (polyMul q a) b hb))

private theorem square_haar_congr (n : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    H n (polyMul p p) ≈ H n (polyMul q q) :=
  haar_of_coeff (RatPolyCoeffEqv.mul h h)

/-- The full finite Cartesian channel family is a coefficient-one contraction
after the matching family of original-coordinate conditional Haar projections. -/
theorem productChannels_familyProject_square_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat) : ∀ (ids : List Nat),
    ids.Nodup → (∀ i, i ∈ ids → i < n) → (q : RatPoly) →
    SupportedQuaternionBlocks n q →
    channelSum (productChannels n w K ids) (fun h =>
      H n (polyMul (familyProject ids (polyMul q h))
        (familyProject ids (polyMul q h)))) ≤ H n (polyMul q q)
  | [], _, _, q, _ => by
      have hunit : RatPolyCoeffEqv (polyMul q polyOne) q :=
        RatPolyCoeffEqv.mul_one q
      have hv := square_haar_congr n hunit
      change 1 * H n (polyMul (polyMul q polyOne) (polyMul q polyOne)) + 0 ≤
        H n (polyMul q q)
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
        (.add (.mul (.const 1) (.var 0)) (.const 0)) (.var 0)
        (by decide) (fun _ => H n (polyMul (polyMul q polyOne) (polyMul q polyOne)))) hv)
  | i :: ids, hnodup, hids, q, hq => by
      have hi : i < n := hids i List.mem_cons_self
      have hnot : i ∉ ids := (List.nodup_cons.mp hnodup).1
      have htailNodup : ids.Nodup := (List.nodup_cons.mp hnodup).2
      have htail : ∀ j, j ∈ ids → j < n :=
        fun j hj => hids j (List.mem_cons_of_mem i hj)
      let target := fun p : RatPoly =>
        H n (polyMul (familyProject (i :: ids) (polyMul q p))
          (familyProject (i :: ids) (polyMul q p)))
      let nested := fun a b : RatPoly =>
        H n (polyMul
          (familyProject ids (polyMul (project i (polyMul q a)) b))
          (familyProject ids (polyMul (project i (polyMul q a)) b)))
      have hflatten := channelSum_multiply target (heatChannels i w K)
        (productChannels n w K ids)
      have hpoint : ∀ a, a ∈ heatChannels i w K →
          channelSum (productChannels n w K ids) (nested a.2) ≤
            H n (polyMul (project i (polyMul q a.2))
              (project i (polyMul q a.2))) := by
        intro a ha
        exact productChannels_familyProject_square_le n hw0 hw1 K ids htailNodup
          htail (project i (polyMul q a.2))
          (project_supported i (supported_polyMul hq
            (heatChannels_supported hi w K a ha)))
      have hnested : channelSum (heatChannels i w K) (fun a =>
          channelSum (productChannels n w K ids) (nested a)) ≤
          channelSum (heatChannels i w K) (fun a =>
            H n (polyMul (project i (polyMul q a))
              (project i (polyMul q a)))) :=
        channelSum_le _ _ _
          (fun a ha => heatChannels_nonnegative hw0 i K a ha) hpoint
      have hone := heatChannels_project_square_le_at n i hi hw0 hw1 K q hq
      have hrewrite : channelSum (multiplyChannels (heatChannels i w K)
          (productChannels n w K ids)) target ≈
          channelSum (heatChannels i w K) (fun a =>
            channelSum (productChannels n w K ids) (nested a)) := by
        exact Q'.eqv_trans _ _ _ hflatten (channelSum_congr _ _ _ (fun a ha =>
          channelSum_congr _ _ _ (fun b hb => square_haar_congr n
            (family_channel_project i ids q a.2 b.2
              (productChannels_independent n w K ids i hnot b hb)))))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite)
        (Q'.le_trans' _ _ _ hnested hone)

/-- A family-independent squared spectator can be retained on both sides of
the same coefficient-one estimate.  This is the unweighted theorem applied to
`q*r`; exact conditional pull-through supplies the displayed form. -/
theorem productChannels_familyProject_weighted_square_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat) (ids : List Nat)
    (hnodup : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (q r : RatPoly) (hq : SupportedQuaternionBlocks n q)
    (hr : SupportedQuaternionBlocks n r)
    (hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i r) :
    channelSum (productChannels n w K ids) (fun h =>
      H n (polyMul
        (polyMul (familyProject ids (polyMul q h))
          (familyProject ids (polyMul q h)))
        (polyMul r r))) ≤
      H n (polyMul (polyMul q q) (polyMul r r)) := by
  have hbase := productChannels_familyProject_square_le n hw0 hw1 K ids
    hnodup hids (polyMul q r) (supported_polyMul hq hr)
  have hvalue : channelSum (productChannels n w K ids) (fun h =>
      H n (polyMul
        (polyMul (familyProject ids (polyMul q h))
          (familyProject ids (polyMul q h))) (polyMul r r))) ≈
      channelSum (productChannels n w K ids) (fun h =>
        H n (polyMul (familyProject ids (polyMul (polyMul q r) h))
          (familyProject ids (polyMul (polyMul q r) h)))) := by
    apply channelSum_congr
    intro c hc
    have hraw : RatPolyCoeffEqv (polyMul (polyMul q r) c.2)
        (polyMul r (polyMul q c.2)) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => q | 1 => r | _ => c.2)
    have hp : RatPolyCoeffEqv
        (familyProject ids (polyMul (polyMul q r) c.2))
        (polyMul r (familyProject ids (polyMul q c.2))) :=
      RatPolyCoeffEqv.trans (familyProject_congr ids hraw)
        (familyProject_mul_of_independent ids r (polyMul q c.2) hind)
    exact haar_of_coeff
      (RatPolyCoeffEqv.trans (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))
        (by decide)
        (fun | 0 => familyProject ids (polyMul q c.2) | _ => r))
          (RatPolyCoeffEqv.mul hp hp).symm)
  have hright : H n (polyMul (polyMul q r) (polyMul q r)) ≈
      H n (polyMul (polyMul q q) (polyMul r r)) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => q | _ => r))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hvalue)
    (Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv hright))

#print axioms YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel.productChannels_familyProject_square_le
#print axioms YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel.productChannels_familyProject_weighted_square_le

end YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
