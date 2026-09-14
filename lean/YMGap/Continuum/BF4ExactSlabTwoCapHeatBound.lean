/-
# Two-cap weights pay either sixteen parity bits or a higher-label rate

Fourteen positive occupations cost at least fourteen parity-plus-quotient
units. After means-42 removal, zero quotient mass forces at least sixteen
parity bits. At the unchanged nome 1/1024, each higher unit can pay for a
missing parity unit and still leaves the explicit rate 9/2^52.
These are original per-pair bounds; aggregate counting is used downstream.
-/

import YMGap.Continuum.BF4ExactSlabTwoCapPairCount

namespace YMGap.Continuum.BF4ExactSlabTwoCapHeatBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FiniteParityHigherProduct
open YMGap.Continuum.SU2ParityHigherHeatEnvelope
open YMGap.Continuum.BF4ExactSlabTwoCapPairCount
open YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48
open YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder
open YMGap.Continuum.BF4ExactSlabSpatialHeatPower42
open YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost (higherCount_zero_small)
open YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound (parityCount_small)
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem positiveCount_le_parity_higher (state : Nat → Nat) : ∀ ids : List Nat,
    positiveCount state ids ≤ parityCount state ids+higherCount state ids
  | [] => Nat.le_refl _
  | id::ids => by
    have ih := positiveCount_le_parity_higher state ids
    by_cases hp : 0 < state id
    all_goals simp only [positiveCount,List.filter_cons,hp,decide_true,decide_false,
      Bool.false_eq_true,↓reduceIte,List.length_cons,parityCount,higherCount] at ih ⊢
    all_goals omega

theorem twoCap_occupation_floor {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ twoCapPairs K margin time) : 14 ≤ pairParity margin pair+pairHigher margin pair := by
  obtain ⟨hg,ids,hs,hm⟩ := twoCapPairs_mem hp
  have ha := original_spatial_minimum_fourteen (shortOtherCores_connected hs) hm hg.2.1
    (Bool.and_eq_true_iff.mp hg.2.2).1
  rw [positiveFaces_length,positiveFaces_length] at ha
  have hl := positiveCount_le_parity_higher pair.1 (slabPhysicalFaceEdges (responseExtent margin))
  have hr := positiveCount_le_parity_higher pair.2 (slabPhysicalFaceEdges (responseExtent margin))
  unfold pairParity pairHigher
  omega

theorem fundamental_casimir_parity (state : Nat → Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → state id ≤ 1) → casimirSum state ids=3*parityCount state ids
  | [], _ => rfl
  | id::ids, hs => by
    have ih := fundamental_casimir_parity state ids (fun j hj => hs j (List.mem_cons_of_mem id hj))
    have hb := hs id List.mem_cons_self
    have he : state id=0 ∨ state id=1 := by omega
    rcases he with he | he
    all_goals simp only [casimirSum,parityCount,he,c4,Nat.zero_add,Nat.zero_mul,ih]
    all_goals omega

theorem twoCap_fundamental_minimum_sixteen {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ twoCapPairs K margin time) (hz : pairHigher margin pair=0) : 16 ≤ pairParity margin pair := by
  obtain ⟨hg,ids,hs,hm⟩ := twoCapPairs_mem hp
  have ha := twoCap_occupation_floor hp
  have hb (id : Nat) (hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)) :
      pair.1 id ≤ 1 ∧ pair.2 id ≤ 1 := by
    unfold pairHigher at hz
    exact ⟨higherCount_zero_small pair.1 _ (by omega) id hi,
      higherCount_zero_small pair.2 _ (by omega) id hi⟩
  have hl := fundamental_casimir_parity pair.1 _ (fun id hi => (hb id hi).1)
  have hr := fundamental_casimir_parity pair.2 _ (fun id hi => (hb id hi).2)
  have hpower : pairPower margin pair=3*pairParity margin pair := by
    unfold pairPower pairParity
    omega
  have heven := nonzero_pairPower_even margin pair hg.2.1
  by_cases h : 16 ≤ pairParity margin pair
  · exact h
  · have he : pairPower margin pair=42 := by omega
    exact False.elim (hg.2.1 (afterMeans42_power42_pairTerm_zero
      (shortOtherCores_connected hs) hm he hg.2.2))

def relativeHigherRate : Q' := 9*Q'.invSucc (2^52-1)

theorem relativeHigher_pin : higherRate nome ≈ oddRate nome*relativeHigherRate := by decide

theorem relativeHigher_nonnegative : (0 : Q') ≤ relativeHigherRate := by decide

theorem qpow_to_pow (w : Q') : ∀ n : Nat, qpow w n ≈ w^n
  | 0 => Q'.eqv_refl 1
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ w (qpow_to_pow w n)) (Q'.mul_comm_eqv _ _)

theorem ratio_power (r s eta : Q') (hs : s ≈ r*eta) (B : Nat) : ∀ H : Nat,
    qpow r B*qpow s H ≈ qpow r (B+H)*eta^H
  | 0 => Q'.eqv_refl _
  | H+1 => by
    rw [Nat.add_succ]
    change qpow r B*(qpow s H*s) ≈ (qpow r (B+H)*r)*(eta*eta^H)
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ s (ratio_power r s eta hs B H)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hs) ?_
    exact poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 3) (.var 1))) (by decide)
      (fun i => if i=0 then qpow r (B+H) else if i=1 then eta^H else if i=2 then r else eta)

theorem twoCap_weight_bound {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ twoCapPairs K margin time) :
    Q'.abs (weightedPairTerm nome K margin pair) ≤
      (8*qpow (oddRate nome) 14)*relativeHigherRate^(pairHigher margin pair) := by
  obtain ⟨_,ids,_,hm⟩ := twoCapPairs_mem hp
  have hpair := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
  have hb := weightedPairTerm_parity_bound (w := nome) (by decide) (by decide) K margin pair
    (fun id _ => bounded K ids pair hpair id)
  have hratio := ratio_power (oddRate nome) (higherRate nome) relativeHigherRate relativeHigher_pin
    (pairParity margin pair) (pairHigher margin pair)
  have hfloor := qpow_antitone (show (0 : Q') ≤ oddRate nome by decide) (by decide)
    14 _ (twoCap_occupation_floor hp)
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left 8 _ _ hratio)) (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 8
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hfloor (Q'.pow_nonneg _ relativeHigher_nonnegative _)) (by decide))
      (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))

theorem twoCap_fundamental_weight_bound {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ twoCapPairs K margin time) (hz : pairHigher margin pair=0) :
    Q'.abs (weightedPairTerm nome K margin pair) ≤ 8*qpow (oddRate nome) 16 := by
  obtain ⟨_,ids,_,hm⟩ := twoCapPairs_mem hp
  have hpair := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
  have hb := weightedPairTerm_parity_bound (w := nome) (by decide) (by decide) K margin pair
    (fun id _ => bounded K ids pair hpair id)
  rw [hz,qpow_zero] at hb
  have hfloor := qpow_antitone (show (0 : Q') ≤ oddRate nome by decide) (by decide)
    16 _ (twoCap_fundamental_minimum_sixteen hp hz)
  exact Q'.le_trans' _ _ _ hb (Q'.mul_le_mul_of_nonneg_left _ _ 8
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hfloor) (by decide))

end YMGap.Continuum.BF4ExactSlabTwoCapHeatBound

#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.positiveCount_le_parity_higher
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.twoCap_occupation_floor
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.fundamental_casimir_parity
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.twoCap_fundamental_minimum_sixteen
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.relativeHigherRate
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.relativeHigher_pin
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.relativeHigher_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.qpow_to_pow
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.ratio_power
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.twoCap_weight_bound
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapHeatBound.twoCap_fundamental_weight_bound
