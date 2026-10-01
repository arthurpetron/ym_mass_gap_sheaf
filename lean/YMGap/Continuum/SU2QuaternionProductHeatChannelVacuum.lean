/-
# Literal vacuum channel and quantitative finite-channel contraction

At nome zero the ORIGINAL finite Cartesian channels evaluate exactly to
the vacuum polynomial for any coefficient-respecting quadratic functional
vanishing at zero. Combined with the computed SU(2) Casimir comparison,
this isolates the unchanged vacuum contribution without dropping any
spectator, normalizer, or omitted cutoff mode.
-/

import YMGap.Continuum.SU2QuaternionProductHeatChannelNomeComparison

namespace YMGap.Continuum.SU2QuaternionProductHeatChannelVacuum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatChannelNomeComparison
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState

local infix:50 " ≈ " => Q'.eqv

private theorem sum_append (F : RatPoly → Q') : ∀ as bs : List GramChannel,
    channelSum (as++bs) F ≈ channelSum as F+channelSum bs F
  | [], _ => (QPoly.q_zero_add_eqv _).symm
  | _::as, bs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_append F as bs))
      (Q'.add_assoc_eqv _ _ _).symm

private theorem sum_flatMap {A : Type} (f : A → List GramChannel)
    (F : RatPoly → Q') : ∀ xs : List A,
    channelSum (xs.flatMap f) F ≈ qListSum (xs.map fun a => channelSum (f a) F)
  | [] => Q'.eqv_refl _
  | _::as => Q'.eqv_trans _ _ _ (sum_append F _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_flatMap f F as))

private theorem sum_congr (F G : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → F c.2 ≈ G c.2) → channelSum cs F ≈ channelSum cs G
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (sum_congr F G cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem sum_zero (F : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → F c.2 ≈ 0) → channelSum cs F ≈ 0
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
        (Q'.mul_zero_eqv _))
      (sum_zero F cs (fun d hd => h d (List.mem_cons_of_mem c hd)))) (by decide)

private theorem sum_zero_weight (F : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → c.1 ≈ 0) → channelSum cs F ≈ 0
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (h c List.mem_cons_self))
        (Q'.zero_mul_eqv _))
      (sum_zero_weight F cs (fun d hd => h d (List.mem_cons_of_mem c hd)))) (by decide)

private theorem qsum_zero (f : Nat → Q') : ∀ ds : List Nat,
    (∀ d, d ∈ ds → f d ≈ 0) → qListSum (ds.map f) ≈ 0
  | [], _ => Q'.eqv_refl _
  | d::ds, h => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (h d List.mem_cons_self)
        (qsum_zero f ds (fun k hk => h k (List.mem_cons_of_mem d hk)))) (by decide)

private theorem qsum_at_zero (f : Nat → Q') : ∀ ds : List Nat,
    ds.Nodup → 0 ∈ ds → (∀ d, d ∈ ds → d ≠ 0 → f d ≈ 0) →
    qListSum (ds.map f) ≈ f 0
  | [], _, hz, _ => False.elim (List.not_mem_nil hz)
  | d::ds, hn, hz, h => by
      by_cases hd : d=0
      · subst d
        exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (qsum_zero f ds (fun k hk => h k (List.mem_cons_of_mem 0 hk)
            (fun he => (List.nodup_cons.mp hn).1 (he ▸ hk))))) (QPoly.q_add_zero_eqv _)
      · have htail : 0 ∈ ds := (List.mem_cons.mp hz).resolve_left
          (fun he => hd he.symm)
        exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
          (h d List.mem_cons_self hd)
          (qsum_at_zero f ds (List.nodup_cons.mp hn).2 htail
            (fun k hk h0 => h k (List.mem_cons_of_mem d hk) h0)))
          (QPoly.q_zero_add_eqv _)

private theorem zero_power {d : Nat} (hd : 0 < d) : qpow (0 : Q') d ≈ 0 := by
  cases d with
  | zero => omega
  | succ d => exact Q'.mul_zero_eqv _

/-- Degree zero has exactly the real unit and imaginary zero leaves. All
positive-degree ORIGINAL weights vanish at nome zero, for every finite K. -/
theorem heatChannels_zero_nome (slot K : Nat) (F : RatPoly → Q')
    (hzero : F polyZero ≈ 0) :
    channelSum (heatChannels slot 0 K) F ≈ F polyOne := by
  let cols := fun d => (List.range (d+1)).flatMap fun k =>
    columnChannels (coeffAt (heatKernelPacket K 0) d) d k
      (polynomialColumn
        (BF4ExactSlabPlaquettePathGram.asRepresentationQuaternion
          (BF4GeometricSpinNetworkMehler.PolyQuaternion.coordinateVariable slot)) d k)
  have hz : channelSum (cols 0) F ≈ F polyOne := by
    change channelSum (columnChannels (coeffAt (heatKernelPacket K 0) 0) 0 0
      (polynomialColumn _ 0 0)) F ≈ F polyOne
    rw [coeffAt_heatKernelPacket (by omega : 0 < K+1), coeffW_zero]
    change 1*F polyOne+(1*F polyZero+0) ≈ F polyOne
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hzero) (Q'.eqv_refl _)))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 1) (.var 0))
          (.add (.mul (.const 1) (.const 0)) (.const 0)))
        (.var 0) (by decide) (fun _ => F polyOne))
  have hp : ∀ d, d ∈ List.range (K+1) → d ≠ 0 → channelSum (cols d) F ≈ 0 := by
    intro d hd h0
    apply sum_zero_weight
    intro c hc
    obtain ⟨k, hk, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    change coeffAt (heatKernelPacket K 0) d * basisInverseWeight d k ≈ 0
    rw [coeffAt_heatKernelPacket (List.mem_range.mp hd)]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (zero_power
          (Nat.mul_pos (by omega : 0 < d) (by omega : 0 < d+2))))
        (Q'.mul_zero_eqv _))) (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ _ _ (sum_flatMap cols F _)
    (Q'.eqv_trans _ _ _ (qsum_at_zero _ _ (CayleyParentInj.range_nodup _)
      (List.mem_range.mpr (by omega)) hp) hz)

private theorem sum_map_multiply (F : RatPoly → Q') (a : GramChannel) : ∀ bs : List GramChannel,
    channelSum (bs.map (multiplyChannel a)) F ≈
      a.1*channelSum bs (fun b => F (polyMul a.2 b))
  | [] => (Q'.mul_zero_eqv _).symm
  | b::bs => Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (sum_map_multiply F a bs))
      (poly_identity_of_normal_eq
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 0) (.var 3)))
        (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3))) (by decide)
        (fun | 0 => a.1 | 1 => b.1 | 2 => F (polyMul a.2 b.2)
             | _ => channelSum bs (fun c => F (polyMul a.2 c))))

private theorem sum_multiply (F : RatPoly → Q') : ∀ as bs : List GramChannel,
    channelSum (multiplyChannels as bs) F ≈
      channelSum as (fun a => channelSum bs (fun b => F (polyMul a b)))
  | [], _ => Q'.eqv_refl _
  | a::as, bs => Q'.eqv_trans _ _ _ (sum_append F _ _)
      (Q'.add_eqv_congr' (sum_map_multiply F a bs) (sum_multiply F as bs))

/-- The ORIGINAL full zero-nome Cartesian sum is exactly its vacuum test.
No arbitrary quotient representative or constant-channel choice is made. -/
theorem productChannels_zero_nome (n K : Nat) : ∀ (ids : List Nat) (F : RatPoly → Q'),
    (∀ p q, RatPolyCoeffEqv p q → F p ≈ F q) → F polyZero ≈ 0 →
    channelSum (productChannels n 0 K ids) F ≈ F polyOne
  | [], F, _, _ => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.eqv_refl _)) (QPoly.q_add_zero_eqv _)
  | i::ids, F, hF, hzero => by
      have hp := sum_congr
        (fun a => channelSum (productChannels n 0 K ids) (fun b => F (polyMul a b)))
        (fun a => F (polyMul a polyOne)) (heatChannels i 0 K)
        (fun c _ => productChannels_zero_nome n K ids (fun b => F (polyMul c.2 b))
          (fun p q h => hF _ _ (h.mul_left c.2))
          (Q'.eqv_trans _ _ _ (hF _ _ (RatPolyCoeffEqv.mul_zero_right _)) hzero))
      exact Q'.eqv_trans _ _ _ (sum_multiply F _ _)
        (Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _
          (heatChannels_zero_nome i K (fun a => F (polyMul a polyOne))
            (Q'.eqv_trans _ _ _ (hF _ _ (RatPolyCoeffEqv.mul_zero_left _)) hzero))
          (hF _ _ (RatPolyCoeffEqv.mul_one _))))

/-- The SAME vacuum polynomial is unchanged; only the nonvacuum channel
contribution receives w^3. This is a finite source/channel comparison. -/
theorem productChannels_vacuum_contraction (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (F : RatPoly → Q')
    (hpos : ∀ p, SupportedQuaternionBlocks n p → (0 : Q') ≤ F p)
    (hF : ∀ p q, RatPolyCoeffEqv p q → F p ≈ F q) (hzero : F polyZero ≈ 0) :
    channelSum (productChannels n w K ids) F ≤
      ((1 : Q')-qpow w 3)*F polyOne +
        qpow w 3*channelSum (productChannels n 1 K ids) F :=
  Q'.le_trans' _ _ _ (productChannels_nome_interpolation n hw0 hw1 K ids hids F hpos)
    (Q'.le_of_eqv (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (productChannels_zero_nome n K ids F hF hzero))
      (Q'.eqv_refl _)))

#print axioms heatChannels_zero_nome
#print axioms productChannels_zero_nome
#print axioms productChannels_vacuum_contraction

end YMGap.Continuum.SU2QuaternionProductHeatChannelVacuum
