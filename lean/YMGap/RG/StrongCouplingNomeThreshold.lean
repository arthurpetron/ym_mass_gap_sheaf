/-
# How far up in `w` does the strong-coupling width-uniform seed reach?

**Label: PROVED threshold + PROVED no-go (V3) for this method. NOT gap evidence.**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs).
Convention: repo nome `w` matches the Numerics `t = -4 ln w`; U(1) is confined only for
w ≤ 1/8 and already Coulomb (massless) at w = 1/2 and 0.5145 (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).

`BF4WilsonAllNomeStrongCouplingUniformRate.allNome_strongCoupling_vacuumSq_all_widths` is already
general in `w`; `w = 1/1024` enters ONLY through its three small-nome guards (`SCGuards`):
`heatRatio w = 32w³ ≤ 1/2`, `δ := heatRemainderBound w = 128w³ < 1`, and the entropy guard
`625 · (2δ + δ²) · (1 - δ)^(-48) < 1` (`entropyRate 625 (adjustedCoreRate w hd) < 1`, with
`adjustedCoreRate = pairedRate δ · inverseFaceFloor^48`). The rate `timeRate = 1/4` does not depend
on `w`. The binding guard is the entropy one: threshold function `T(δ) = 625·(2δ+δ²)·(1-δ)^(-48)`.

* `guards_of_delta_le`: `T(δ0) < 1`, `δ0 ≤ 1/2`, `heatRemainderBound w ≤ δ0` ⇒ `SCGuards w`.
* `scGuards_of_le_inv55` / `uniformSeedGap_of_le_inv55`: PROVED for every `0 < w ≤ 1/55`
  (largest dyadic: `w = 1/64`), with rate `timeRate = 1/4`.
* `not_scGuards_of_inv54_le`: FAILS for every `w ≥ 1/54` (already `625·2δ ≥ 1`). So the
  dyadic points `1/32, 1/16, 1/8, 1/4, 1/2` are out of reach of this method. Bottleneck constant:
  the core-count degree `625` against the paired heat rate `2·128·w³`. Even without it, `δ < 1`
  needs `w < 128^(-1/3) ≈ 0.198`, and `heatRatio ≤ 1/2` needs `w ≤ 1/4`; `w = 1/2` gives `δ = 16`.

Constructive, no external library; axioms within `propext`, `Quot.sound`.
-/

import YMGap.RG.UniformSeedGap
import YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate

namespace YMGap.RG.StrongCouplingNomeThreshold

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.QuaternionHaarCharacterInterval
  (heatRatio heatRemainderBound heatRemainderBound_eq heatRemainderBound_nonnegative)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
  (adjustedCoreRate inverseFaceFloor inverseFaceFloor_pos one_le_inverseFaceFloor)
open YMGap.Continuum.PolynomialBiadditiveMobius (pairedRate)
open YMGap.Continuum.FiniteSizeGeometricSum (entropyRate)
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay (timeRate timeRate_lt_one)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.RG.UniformSeedGap (UniformSeedGap)

/-- The three small-nome guards of the strong-coupling uniform-rate theorem.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
def SCGuards (w : Q') : Prop :=
  heatRatio w ≤ HalfPow.half ∧
    ∃ hd : heatRemainderBound w < 1, entropyRate 625 (adjustedCoreRate w hd) < 1

/-- Threshold function `T(δ) = 625·(2δ+δ²)·(1-δ)^(-48)`, `δ = 128w³`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
def threshold (d : Q') (hd : d < 1) : Q' :=
  entropyRate 625 (pairedRate d * (Q'.recipPos (1 + -d) (YMGap.Continuum.HKPos.one_sub_pos hd))^48)

/-- **Guards ⇒ width-uniform rate `timeRate = 1/4` at `w` (PROVED, existing theorem).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem uniformRate_of_guards {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hG : SCGuards w) : ∀ width : Nat, WilsonVacuumSqContraction hw0 hw1 width timeRate :=
  let ⟨hs, hd, he⟩ := hG
  YMGap.Continuum.BF4WilsonAllNomeStrongCouplingUniformRate.allNome_strongCoupling_vacuumSq_all_widths
    hw0 hw1 hs hd he

/-- **Guards ⇒ `UniformSeedGap` for every `budget < timeRate` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem uniformSeedGap_of_guards {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hG : SCGuards w) (budget : Q') (hb : budget < timeRate) : UniformSeedGap hw0 hw1 budget :=
  ⟨timeRate, hb, timeRate_lt_one, uniformRate_of_guards hw0 hw1 hG⟩

private theorem heatRatio_le_remainder {w : Q'} (hw : (0 : Q') ≤ w) :
    heatRatio w ≤ heatRemainderBound w := by
  have hq := qpow_nonneg w hw 3
  have e : Q'.eqv ((2 * qpow w 3) * 16) (32 * qpow w 3) :=
    poly_identity_of_normal_eq (.mul (.mul (.const 2) (.var 0)) (.const 16))
      (.mul (.const 32) (.var 0)) (by decide) (fun _ => qpow w 3)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : (32 : Q') ≤ 128) hq)
      (Q'.ge_of_eqv (heatRemainderBound_eq w)))

private theorem pairedRate_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    pairedRate a ≤ pairedRate b :=
  Q'.add_le_add (Q'.add_le_add hab hab)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hab ha)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hab (Q'.le_trans' _ _ _ ha hab)))

private theorem q_lt_irrefl (a : Q') : ¬ a < a := fun h => by
  have e : a.num * (a.den : Int) < a.num * (a.den : Int) := h
  exact Int.lt_irrefl _ e

/-- **Closed-form threshold (PROVED).** `δ(w) ≤ δ0 ≤ 1/2` and `T(δ0) < 1` give all guards.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem guards_of_delta_le {w d0 : Q'} (hw : (0 : Q') ≤ w) (hd0 : d0 < 1)
    (hhalf : d0 ≤ HalfPow.half) (hle : heatRemainderBound w ≤ d0) (hT : threshold d0 hd0 < 1) :
    SCGuards w := by
  have hδ0 := heatRemainderBound_nonnegative hw
  have hd : heatRemainderBound w < 1 := Q'.lt_of_le_of_lt hle hd0
  refine ⟨Q'.le_trans' _ _ _ (heatRatio_le_remainder hw) (Q'.le_trans' _ _ _ hle hhalf), hd, ?_⟩
  have hr : inverseFaceFloor w hd ≤ Q'.recipPos (1 + -d0) (YMGap.Continuum.HKPos.one_sub_pos hd0) :=
    YMGap.Continuum.ChebOrthoBracketDecay.recipPos_antitone _ _
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hle))
  have hp := CRealLog.pow_le_pow_base _ _ (Q'.le_of_lt (inverseFaceFloor_pos w hd)) hr 48
  have hpd := pairedRate_mono hδ0 hle
  have hadj : adjustedCoreRate w hd ≤
      pairedRate d0 * (Q'.recipPos (1 + -d0) (YMGap.Continuum.HKPos.one_sub_pos hd0))^48 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hpd
        (Q'.pow_nonneg _ (Q'.le_of_lt (inverseFaceFloor_pos w hd)) 48))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hp
        (Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ pairedRate 0)
          (pairedRate_mono (Q'.le_refl' 0) (Q'.le_trans' _ _ _ hδ0 hle))))
  exact Q'.lt_of_le_of_lt
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hadj (YMGap.Continuum.ClusterCount.ofNat_nonneg 625)) hT

private theorem qpow_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ n, qpow a n ≤ qpow b n
  | 0 => Q'.le_refl' _
  | n+1 => Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (qpow_mono ha hab n) ha)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hab (qpow_nonneg b (Q'.le_trans' _ _ _ ha hab) n))

private theorem remainder_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    heatRemainderBound a ≤ heatRemainderBound b :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (heatRemainderBound_eq a))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_mono ha hab 3) (by decide))
      (Q'.ge_of_eqv (heatRemainderBound_eq b)))

/-- `w = 1/55`. -/
def inv55 : Q' := Q'.mkPos 1 55 (by decide)
/-- `w = 1/54`. -/
def inv54 : Q' := Q'.mkPos 1 54 (by decide)

/-- **`T(δ(1/55)) < 1` (decidable, cheap).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem threshold_inv55 : threshold (heatRemainderBound inv55) (by decide) < 1 := by
  decide +kernel

/-- **All guards for every `0 ≤ w ≤ 1/55` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem scGuards_of_le_inv55 {w : Q'} (hw : (0 : Q') ≤ w) (h : w ≤ inv55) : SCGuards w :=
  guards_of_delta_le hw (by decide) (by decide) (remainder_mono hw h) threshold_inv55

/-- **Width-uniform seed for every `0 < w ≤ 1/55`, every `budget < timeRate = 1/4` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem uniformSeedGap_of_le_inv55 {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (h : w ≤ inv55) (budget : Q') (hb : budget < timeRate) : UniformSeedGap hw0 hw1 budget :=
  uniformSeedGap_of_guards hw0 hw1 (scGuards_of_le_inv55 (Q'.le_of_lt hw0) h) budget hb

/-- **Largest dyadic instance: `w = 1/64` (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem uniformSeedGap_inv64 (budget : Q') (hb : budget < timeRate) :
    UniformSeedGap (w := Q'.mkPos 1 64 (by decide)) (by decide) (by decide) budget :=
  uniformSeedGap_of_le_inv55 _ _ (by decide) budget hb

/-- `timeRate = 1/4` (the rate at every `w ≤ 1/55`, independent of `w`).
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem timeRate_eq : Q'.eqv timeRate (Q'.mkPos 1 4 (by decide)) := by decide

/-- **V3 no-go for this method (PROVED).** For every `w ≥ 1/54` the entropy guard fails for
every proof `hd`: already `625·pairedRate(δ) ≥ 1` since `inverseFaceFloor ≥ 1`.
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem not_scGuards_of_inv54_le {w : Q'} (h : inv54 ≤ w) : ¬ SCGuards w := by
  intro ⟨_, hd, he⟩
  have hw : (0 : Q') ≤ w := Q'.le_trans' _ _ _ (by decide) h
  have hδ := remainder_mono (by decide) h
  have hδ0 := heatRemainderBound_nonnegative (w := inv54) (by decide)
  have hpd := pairedRate_mono hδ0 hδ
  have h1 : (1 : Q') ≤ (inverseFaceFloor w hd)^48 :=
    Q'.le_trans' _ _ _ (by decide +kernel : (1 : Q') ≤ (1 : Q')^48)
      (CRealLog.pow_le_pow_base _ _ (by decide) (one_le_inverseFaceFloor hw hd) 48)
  have hpw : (0 : Q') ≤ pairedRate (heatRemainderBound w) :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ pairedRate 0)
      (pairedRate_mono (Q'.le_refl' 0) (heatRemainderBound_nonnegative hw))
  have hadj : pairedRate (heatRemainderBound inv54) ≤ adjustedCoreRate w hd :=
    Q'.le_trans' _ _ _ hpd
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ h1 hpw))
  have hbase : (1 : Q') ≤ entropyRate 625 (pairedRate (heatRemainderBound inv54)) := by decide
  have hge : (1 : Q') ≤ entropyRate 625 (adjustedCoreRate w hd) :=
    Q'.le_trans' _ _ _ hbase
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hadj (YMGap.Continuum.ClusterCount.ofNat_nonneg 625))
  exact q_lt_irrefl _ (Q'.lt_of_le_of_lt hge he)

/-- **The dyadic points `1/32, 1/16, 1/8, 1/4, 1/2` are out of reach (PROVED).**
U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem not_scGuards_dyadic :
    ¬ SCGuards (Q'.mkPos 1 32 (by decide)) ∧ ¬ SCGuards (Q'.mkPos 1 16 (by decide)) ∧
      ¬ SCGuards (Q'.mkPos 1 8 (by decide)) ∧ ¬ SCGuards (Q'.mkPos 1 4 (by decide)) ∧
      ¬ SCGuards HalfPow.half :=
  ⟨not_scGuards_of_inv54_le (by decide), not_scGuards_of_inv54_le (by decide),
   not_scGuards_of_inv54_le (by decide), not_scGuards_of_inv54_le (by decide),
   not_scGuards_of_inv54_le (by decide)⟩

/-- **Independent of the entropy count, `w = 1/4` and `w = 1/2` already break `δ < 1`
(decidable).** U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β;
YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). -/
theorem remainder_ge_one_quarter_half :
    ¬ heatRemainderBound (Q'.mkPos 1 4 (by decide)) < 1 ∧ ¬ heatRemainderBound HalfPow.half < 1 :=
  ⟨by decide, by decide⟩

end YMGap.RG.StrongCouplingNomeThreshold
