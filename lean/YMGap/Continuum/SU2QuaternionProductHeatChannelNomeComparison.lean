/-
# Casimir-tagged comparison of the ORIGINAL finite Gram channels

The computed tags retain every real/imaginary representation-column leaf,
its inverse basis weight, and the finite cutoff. Cartesian multiplication
adds Casimirs. Every nonzero SU(2) charge is at least three, so the literal
channel sum is bounded by its nome-zero vacuum contribution plus w^3 times
its nome-one nonvacuum contribution. No interacting variance comparison,
OS operator gap, or scaling estimate is assumed or asserted here.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
import YMGap.Continuum.HeatKernelRGStep

namespace YMGap.Continuum.SU2QuaternionProductHeatChannelNomeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

/-- Computed bookkeeping for an existing literal Gram channel, not a new
analytic input. The polynomial and inverse-weight normalizer are retained. -/
structure SpectralChannel where
  charge : Nat
  weight : Q'
  polynomial : RatPoly

def spectralHeatChannels (slot K : Nat) : List SpectralChannel :=
  (List.range (K+1)).flatMap fun d =>
    (List.range (d+1)).flatMap fun k =>
      (tensorLeaves d (polynomialColumn
        (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) d k)).map
        fun p => ⟨c4 d, dimQ d * basisInverseWeight d k, p⟩

def spectralMultiply (a b : SpectralChannel) : SpectralChannel :=
  ⟨a.charge+b.charge, a.weight*b.weight, polyMul a.polynomial b.polynomial⟩

def spectralProductChannels (K : Nat) : List Nat → List SpectralChannel
  | [] => [⟨0, 1, polyOne⟩]
  | i :: ids => (spectralHeatChannels i K).flatMap fun a =>
      (spectralProductChannels K ids).map fun b => spectralMultiply a b

def atNome (w : Q') (a : SpectralChannel) : GramChannel :=
  (qpow w a.charge * a.weight, a.polynomial)

private inductive ListRel (R : GramChannel → GramChannel → Prop) :
    List GramChannel → List GramChannel → Prop where
  | nil : ListRel R [] []
  | cons {a b as bs} : R a b → ListRel R as bs → ListRel R (a::as) (b::bs)

private def ChannelEqv (a b : GramChannel) : Prop := a.1 ≈ b.1 ∧ a.2 = b.2

private theorem rel_map {A : Type} (f g : A → GramChannel)
    (h : ∀ a, ChannelEqv (f a) (g a)) : ∀ xs : List A,
    ListRel ChannelEqv (xs.map f) (xs.map g)
  | [] => .nil
  | a::as => .cons (h a) (rel_map f g h as)

private theorem rel_append {as bs cs ds : List GramChannel}
    (h : ListRel ChannelEqv as bs) (k : ListRel ChannelEqv cs ds) :
    ListRel ChannelEqv (as++cs) (bs++ds) := by
  induction h with
  | nil => exact k
  | cons ha ht ih => exact .cons ha ih

private theorem rel_flatMap {A : Type} (f g : A → List GramChannel) : ∀ xs : List A,
    (∀ a, a ∈ xs → ListRel ChannelEqv (f a) (g a)) →
    ListRel ChannelEqv (xs.flatMap f) (xs.flatMap g)
  | [], _ => .nil
  | a::as, h => rel_append (h a List.mem_cons_self)
      (rel_flatMap f g as (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem multiply_congr {a b c d : GramChannel}
    (h : ChannelEqv a b) (k : ChannelEqv c d) :
    ChannelEqv (multiplyChannel a c) (multiplyChannel b d) :=
  ⟨Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h.1)
    (Q'.mul_eqv_congr_left _ _ _ k.1),
    (congrArg (fun p => polyMul p c.2) h.2).trans
      (congrArg (fun p => polyMul b.2 p) k.2)⟩

private theorem rel_map_multiply {as bs : List GramChannel}
    (h : ListRel ChannelEqv as bs) {a b : GramChannel} (hab : ChannelEqv a b) :
    ListRel ChannelEqv (as.map (multiplyChannel a))
      (bs.map (multiplyChannel b)) := by
  induction h with
  | nil => exact .nil
  | cons hx ht ih => exact .cons (multiply_congr hab hx) ih

private theorem rel_multiply {as bs cs ds : List GramChannel}
    (h : ListRel ChannelEqv as bs) (k : ListRel ChannelEqv cs ds) :
    ListRel ChannelEqv (multiplyChannels as cs) (multiplyChannels bs ds) := by
  induction h with
  | nil => exact .nil
  | cons ha ht ih => exact rel_append (rel_map_multiply k ha) ih

private theorem rel_trans {as bs cs : List GramChannel}
    (h : ListRel ChannelEqv as bs) (k : ListRel ChannelEqv bs cs) :
    ListRel ChannelEqv as cs := by
  induction h generalizing cs with
  | nil => cases k; exact .nil
  | cons ha ht ih =>
      cases k with
      | cons ka kt =>
          exact .cons ⟨Q'.eqv_trans _ _ _ ha.1 ka.1, ha.2.trans ka.2⟩ (ih kt)

private theorem heat_channels_pin (slot : Nat) (w : Q') (K : Nat) :
    ListRel ChannelEqv ((spectralHeatChannels slot K).map (atNome w))
      (heatChannels slot w K) := by
  unfold spectralHeatChannels heatChannels
  simp only [List.map_flatMap, List.map_map]
  apply rel_flatMap
  intro d hd
  apply rel_flatMap
  intro k hk
  unfold columnChannels
  apply rel_map
  intro p
  constructor
  · change qpow w (c4 d) * (dimQ d * basisInverseWeight d k) ≈
      coeffAt (heatKernelPacket K w) d * basisInverseWeight d k
    rw [coeffAt_heatKernelPacket (List.mem_range.mp hd)]
    exact poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
      (fun | 0 => qpow w (c4 d) | 1 => dimQ d | _ => basisInverseWeight d k)
  · rfl

private theorem atNome_multiply (w : Q') (a b : SpectralChannel) :
    ChannelEqv (atNome w (spectralMultiply a b))
      (multiplyChannel (atNome w a) (atNome w b)) := by
  constructor
  · change qpow w (a.charge+b.charge)*(a.weight*b.weight) ≈
      (qpow w a.charge*a.weight)*(qpow w b.charge*b.weight)
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (qpow_add w a.charge b.charge))
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun
          | 0 => qpow w a.charge
          | 1 => qpow w b.charge
          | 2 => a.weight
          | _ => b.weight))
  · rfl

private theorem product_channels_pin (n : Nat) (w : Q') (K : Nat) : ∀ ids,
    ListRel ChannelEqv ((spectralProductChannels K ids).map (atNome w))
      (productChannels n w K ids)
  | [] => .cons ⟨Q'.mul_one_eqv _, rfl⟩ .nil
  | i::ids => by
      have hflat : ListRel ChannelEqv
          ((spectralProductChannels K (i::ids)).map (atNome w))
          (multiplyChannels ((spectralHeatChannels i K).map (atNome w))
            ((spectralProductChannels K ids).map (atNome w))) := by
        change ListRel ChannelEqv
          (((spectralHeatChannels i K).flatMap fun a =>
            (spectralProductChannels K ids).map fun b => spectralMultiply a b).map (atNome w))
          (multiplyChannels ((spectralHeatChannels i K).map (atNome w))
            ((spectralProductChannels K ids).map (atNome w)))
        unfold multiplyChannels
        simp only [List.map_flatMap, List.flatMap_map, List.map_map]
        apply rel_flatMap
        intro a ha
        exact rel_map _ _ (fun b => atNome_multiply w a b) _
      exact rel_trans hflat (rel_multiply (heat_channels_pin i w K)
        (product_channels_pin n w K ids))

private theorem rel_sum (F : RatPoly → Q') {as bs : List GramChannel}
    (h : ListRel ChannelEqv as bs) : channelSum as F ≈ channelSum bs F := by
  induction h with
  | nil => exact Q'.eqv_refl _
  | cons ha ht ih =>
      exact Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha.1)
          (ha.2 ▸ Q'.eqv_refl _)) ih

/-- Evaluation of the computed tags is the literal ORIGINAL product channel
sum. No positivity, cutoff guard or distinctness premise enters this pin. -/
theorem product_channel_sum_pin (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (F : RatPoly → Q') :
    qListSum ((spectralProductChannels K ids).map fun a =>
      (qpow w a.charge*a.weight)*F a.polynomial) ≈
      channelSum (productChannels n w K ids) F := by
  have h := rel_sum F (product_channels_pin n w K ids)
  simpa only [channelSum, List.map_map, atNome] using h

private theorem heat_channel_budget (slot K : Nat) : ∀ a,
    a ∈ spectralHeatChannels slot K →
    (a.charge=0 ∨ 3 ≤ a.charge) ∧ (0 : Q') ≤ a.weight := by
  intro a ha
  obtain ⟨d, hd, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨k, hk, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  constructor
  · by_cases h : d=0
    · subst d; exact Or.inl rfl
    · exact Or.inr (Nat.mul_le_mul (by omega : 1 ≤ d) (by omega : 3 ≤ d+2))
  · exact Q'.mul_nonneg _ _ (dimQ_nonneg d)
      (Q'.le_of_lt (basisInverseWeight_pos d k))

private theorem product_channel_budget (K : Nat) : ∀ ids a,
    a ∈ spectralProductChannels K ids →
    (a.charge=0 ∨ 3 ≤ a.charge) ∧ (0 : Q') ≤ a.weight
  | [], a, ha => by
      obtain rfl := List.mem_singleton.mp ha
      exact ⟨Or.inl rfl, by decide⟩
  | i::ids, a, ha => by
      obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      have h := heat_channel_budget i K b hb
      have k := product_channel_budget K ids c hc
      constructor
      · change b.charge+c.charge=0 ∨ 3 ≤ b.charge+c.charge
        rcases h.1 with h0 | h3
        · rcases k.1 with k0 | k3
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      · exact Q'.mul_nonneg _ _ h.2 k.2

private theorem rel_supported {n : Nat} {as bs : List GramChannel}
    (h : ListRel ChannelEqv as bs)
    (hs : ∀ b, b ∈ bs → SupportedQuaternionBlocks n b.2) :
    ∀ a, a ∈ as → SupportedQuaternionBlocks n a.2 := by
  induction h with
  | nil => intro a ha; contradiction
  | cons hab ht ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hab.2 ▸ hs _ List.mem_cons_self
      · exact ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) a ha

private theorem zero_power {d : Nat} (hd : 0 < d) : qpow (0 : Q') d ≈ 0 := by
  cases d with
  | zero => omega
  | succ d => exact Q'.mul_zero_eqv _

private theorem one_power : ∀ d, qpow (1 : Q') d ≈ 1
  | 0 => Q'.eqv_refl _
  | d+1 => Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (one_power d)

private theorem channel_interpolation {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (a : SpectralChannel) (F : RatPoly → Q')
    (ha : a.charge=0 ∨ 3 ≤ a.charge)
    (hweight : (0 : Q') ≤ a.weight) (hF : (0 : Q') ≤ F a.polynomial) :
    (qpow w a.charge*a.weight)*F a.polynomial ≤
      ((1 : Q')-qpow w 3)*((qpow 0 a.charge*a.weight)*F a.polynomial) +
        qpow w 3*((qpow 1 a.charge*a.weight)*F a.polynomial) := by
  rcases ha with h0 | h3
  · rw [h0, qpow_zero, qpow_zero, qpow_zero]
    exact Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.const 1) (.var 0)) (.var 1))
      (.add (.mul (.add (.const 1) (.neg (.var 2)))
        (.mul (.mul (.const 1) (.var 0)) (.var 1)))
        (.mul (.var 2) (.mul (.mul (.const 1) (.var 0)) (.var 1))))
      (by decide) (fun | 0 => a.weight | 1 => F a.polynomial | _ => qpow w 3))
  · have hp := Q'.mul_nonneg _ _ hweight hF
    have hle := Q'.mul_le_mul_of_nonneg_right _ _ _
      (qpow_antitone hw0 hw1 3 a.charge h3) hp
    have hleft : (qpow w a.charge*a.weight)*F a.polynomial ≈
        qpow w a.charge*(a.weight*F a.polynomial) := Q'.mul_assoc_eqv _ _ _
    have hright :
        ((1 : Q')-qpow w 3)*((qpow 0 a.charge*a.weight)*F a.polynomial) +
          qpow w 3*((qpow 1 a.charge*a.weight)*F a.polynomial) ≈
        qpow w 3*(a.weight*F a.polynomial) := by
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (zero_power (by omega)))))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (one_power a.charge)))))
        (poly_identity_of_normal_eq
          (.add (.mul (.add (.const 1) (.neg (.var 2)))
            (.mul (.mul (.const 0) (.var 0)) (.var 1)))
            (.mul (.var 2) (.mul (.mul (.const 1) (.var 0)) (.var 1))))
          (.mul (.var 2) (.mul (.var 0) (.var 1)))
          (by decide) (fun | 0 => a.weight | 1 => F a.polynomial | _ => qpow w 3))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hle (Q'.ge_of_eqv hright))

private theorem sum_interpolation (w : Q') (F : RatPoly → Q') :
    ∀ cs : List SpectralChannel,
    (∀ a, a ∈ cs →
      (qpow w a.charge*a.weight)*F a.polynomial ≤
        ((1 : Q')-qpow w 3)*((qpow 0 a.charge*a.weight)*F a.polynomial) +
          qpow w 3*((qpow 1 a.charge*a.weight)*F a.polynomial)) →
    qListSum (cs.map fun a : SpectralChannel =>
      (qpow w a.charge*a.weight)*F a.polynomial) ≤
      ((1 : Q')-qpow w 3)*qListSum (cs.map fun a =>
        (qpow 0 a.charge*a.weight)*F a.polynomial) +
        qpow w 3*qListSum (cs.map fun a =>
          (qpow 1 a.charge*a.weight)*F a.polynomial)
  | [], _ => by
      apply Q'.le_of_eqv
      change (0 : Q') ≈ (1-qpow w 3)*0+qpow w 3*0
      exact poly_identity_of_normal_eq (.const 0)
        (.add (.mul (.add (.const 1) (.neg (.var 0))) (.const 0))
          (.mul (.var 0) (.const 0))) (by decide) (fun _ => qpow w 3)
  | a::as, h => Q'.le_trans' _ _ _
      (Q'.add_le_add (h a List.mem_cons_self)
        (sum_interpolation w F as (fun b hb => h b (List.mem_cons_of_mem a hb))))
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.add (.mul (.var 0) (.var 4)) (.mul (.var 2) (.var 5))))
        (.add (.mul (.var 0) (.add (.var 1) (.var 4)))
          (.mul (.var 2) (.add (.var 3) (.var 5)))) (by decide)
        (fun | 0 => (1 : Q')-qpow w 3
             | 1 => (qpow 0 a.charge*a.weight)*F a.polynomial
             | 2 => qpow w 3
             | 3 => (qpow 1 a.charge*a.weight)*F a.polynomial
             | 4 => qListSum (as.map fun b => (qpow 0 b.charge*b.weight)*F b.polynomial)
             | _ => qListSum (as.map fun b => (qpow 1 b.charge*b.weight)*F b.polynomial))))

/-- Quantitative finite-channel contraction relative to the SAME vacuum
channel contribution. Nonzero SU(2) Casimirs, not channel count, give w^3.
Every K, including zero, is allowed. Selected blocks may repeat. -/
theorem productChannels_nome_interpolation (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (F : RatPoly → Q')
    (hF : ∀ p, SupportedQuaternionBlocks n p → (0 : Q') ≤ F p) :
    channelSum (productChannels n w K ids) F ≤
      ((1 : Q')-qpow w 3)*channelSum (productChannels n 0 K ids) F +
        qpow w 3*channelSum (productChannels n 1 K ids) F := by
  let cs := spectralProductChannels K ids
  have hs := rel_supported (product_channels_pin n 1 K ids)
    (productChannels_supported n 1 K ids hids)
  have h := sum_interpolation w F cs (fun a ha =>
    channel_interpolation hw0 hw1 a F (product_channel_budget K ids a ha).1
      (product_channel_budget K ids a ha).2
      (hF a.polynomial (hs (atNome 1 a) (List.mem_map.mpr ⟨a,ha,rfl⟩))))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (product_channel_sum_pin n w K ids F))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (product_channel_sum_pin n 0 K ids F))
      (Q'.mul_eqv_congr_left _ _ _ (product_channel_sum_pin n 1 K ids F)))))

#print axioms product_channel_sum_pin
#print axioms productChannels_nome_interpolation

end YMGap.Continuum.SU2QuaternionProductHeatChannelNomeComparison
