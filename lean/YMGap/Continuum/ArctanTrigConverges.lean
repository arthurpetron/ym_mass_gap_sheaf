/-
# Closing the antitone-modulus residual for `at5` (`At5Modulus` discharged)

This module removes ONE of the two Type-level residuals carried by
`ArctanSeriesTrigBridge`: the antitone Cauchy-modulus datum `At5Modulus` for
`Pi.at5 = arctan(1/5)`.  It constructs a CONCRETE such datum `at5Modulus`, so
the modulus is no longer an assumed input; the only remaining honest atom for the
arctan↔trig bridge is the transcendental cross-series convergence
`ArctanSeriesTrigBridge.ArctanTrigConverges` (a genuine composed-Taylor identity
that a limit-uniqueness / series-composition shortcut cannot manufacture; it
would require a dedicated ODE-uniqueness module).

## What is genuinely proved here

* `atMw ε := ε.den / ε.num.toNat` — the Nat floor of `1/ε`, a value-based
  (hence antitone) Cauchy stage, unlike the naive `ε.den`.
* `ratioPow_mul_H_le_stage` (**Lemma A**) — the stage-parametrized modulus bound
  `r^N · H ≤ ε` whenever `invSucc N ≤ ε` (`r = 1/k^4 ≤ 1/2`, `0 ≤ H ≤ 1`).
* `cPart_cauchy_stage` (**Lemma B**) — the two-sided directional Cauchy property
  of the arctan partial sums `cPart k` at an arbitrary stage `N` with modulus
  `r^N·H ≤ ε`.
* `atMw_invSucc_le`, `atMw_antitone` (**Lemma C**) — the two elementary Nat
  floor-division facts: `invSucc (atMw ε) ≤ ε` and antitonicity of `atMw`.
* `at5Modulus : ArctanSeriesTrigBridge.At5Modulus` — the assembled datum.
* `sinCat5`, `cosCat5`, `tanLink_at5` — the bridge objects/identity at the now
  CONCRETE modulus, conditional ONLY on `ArctanTrigConverges`.

## Axiom gate

Every declaration reports `[propext]`/`[propext, Quot.sound]` only (the Nat/Int
arithmetic uses `omega`, permitted here per the module's `Quot.sound` gate).  No
`Classical.*`, no `sorry`, no new axiom.
-/

import YMGap.Continuum.ArctanSeriesTrigBridge
import YMGap.Constructive.Pi
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.ArctanTrigConverges

open YMGap.Constructive
open YMGap.Continuum

/-! ## 0. Small Nat/Int helpers (local, self-contained) -/

/-- Positive numerator is preserved upward: `0 < q.num → q ≤ r → 0 < r.num`. -/
theorem posNum_of_le {q r : Q'} (hq : 0 < q.num) (h : q ≤ r) : 0 < r.num := by
  have hcross : q.num * (r.den : Int) ≤ r.num * (q.den : Int) := h
  have hqd : (0 : Int) < (q.den : Int) := by exact_mod_cast q.den_pos
  have hrd : (0 : Int) < (r.den : Int) := by exact_mod_cast r.den_pos
  rcases Int.lt_or_le 0 r.num with hr | hr
  · exact hr
  · have hLpos : (0 : Int) < q.num * (r.den : Int) := Int.mul_pos hq hrd
    have hRnonpos : r.num * (q.den : Int) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg hr (Int.le_of_lt hqd)
    omega

/-- Nat floor-division monotonicity from a cross-multiplied bound:
for positive `b, d`, `a·d ≤ c·b → a / b ≤ c / d`. -/
theorem nat_div_le_div_of_cross {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  rw [Nat.le_div_iff_mul_le hd]
  have hdiv : a / b * b ≤ a := Nat.div_mul_le_self a b
  have hstep : (a / b * d) * b ≤ c * b := by
    have he : (a / b * d) * b = (a / b * b) * d := by rw [Nat.mul_right_comm]
    rw [he]
    exact Nat.le_trans (Nat.mul_le_mul_right d hdiv) h
  exact Nat.le_of_mul_le_mul_right hstep hb

/-- Extract `0 < ε.num` from `0 < ε`. -/
theorem num_pos_of_pos {ε : Q'} (hε : (0 : Q') < ε) : (0 : Int) < ε.num := by
  have h : (0 : Int) * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
  rw [Int.zero_mul] at h
  have h' : (0 : Int) < ε.num * 1 := h
  rwa [Int.mul_one] at h'

/-! ## 1. The antitone modulus `atMw ε = ⌊1/ε⌋` -/

/-- The Nat floor of `1/ε`: `ε.den / ε.num.toNat`.  A value-based (hence
antitone) Cauchy stage for `at5`. -/
def atMw (ε : Q') : Nat := ε.den / ε.num.toNat

/-- **Lemma C.1.** `invSucc (atMw ε) ≤ ε` for `0 < ε`. -/
theorem atMw_invSucc_le (ε : Q') (hε : (0 : Q') < ε) :
    Q'.invSucc (atMw ε) ≤ ε := by
  have hnum_pos : (0 : Int) < ε.num := num_pos_of_pos hε
  have ha_pos : 0 < ε.num.toNat := by
    have h : (0 : Int) < (ε.num.toNat : Int) := by
      rw [Int.toNat_of_nonneg (Int.le_of_lt hnum_pos)]; exact hnum_pos
    exact_mod_cast h
  have hnat : ε.den ≤ ε.num.toNat * (ε.den / ε.num.toNat + 1) := by
    have h1 : ε.num.toNat * (ε.den / ε.num.toNat) + ε.den % ε.num.toNat = ε.den :=
      Nat.div_add_mod ε.den ε.num.toNat
    have h2 : ε.den % ε.num.toNat < ε.num.toNat := Nat.mod_lt ε.den ha_pos
    have h3 : ε.num.toNat * (ε.den / ε.num.toNat + 1)
        = ε.num.toNat * (ε.den / ε.num.toNat) + ε.num.toNat := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  have hnumeq : ε.num = (ε.num.toNat : Int) :=
    (Int.toNat_of_nonneg (Int.le_of_lt hnum_pos)).symm
  show (Q'.invSucc (atMw ε)).num * (ε.den : Int)
      ≤ ε.num * ((Q'.invSucc (atMw ε)).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_den, Int.one_mul, hnumeq]
  show (ε.den : Int) ≤ (ε.num.toNat : Int) * ((ε.den / ε.num.toNat + 1 : Nat) : Int)
  exact_mod_cast hnat

/-- **Lemma C.2.** `atMw` is antitone: `0 < δ → δ ≤ ε → atMw ε ≤ atMw δ`. -/
theorem atMw_antitone (ε δ : Q') (hδ : (0 : Q') < δ) (hδε : δ ≤ ε) :
    atMw ε ≤ atMw δ := by
  have hδnum : (0 : Int) < δ.num := num_pos_of_pos hδ
  have hεnum : (0 : Int) < ε.num := posNum_of_le hδnum hδε
  have hδtoNat : 0 < δ.num.toNat := by
    have h : (0 : Int) < (δ.num.toNat : Int) := by
      rw [Int.toNat_of_nonneg (Int.le_of_lt hδnum)]; exact hδnum
    exact_mod_cast h
  have hεtoNat : 0 < ε.num.toNat := by
    have h : (0 : Int) < (ε.num.toNat : Int) := by
      rw [Int.toNat_of_nonneg (Int.le_of_lt hεnum)]; exact hεnum
    exact_mod_cast h
  have hcross : δ.num * (ε.den : Int) ≤ ε.num * (δ.den : Int) := hδε
  have hnatcross : δ.num.toNat * ε.den ≤ ε.num.toNat * δ.den := by
    have e1 : δ.num = (δ.num.toNat : Int) :=
      (Int.toNat_of_nonneg (Int.le_of_lt hδnum)).symm
    have e2 : ε.num = (ε.num.toNat : Int) :=
      (Int.toNat_of_nonneg (Int.le_of_lt hεnum)).symm
    rw [e1, e2] at hcross
    exact_mod_cast hcross
  show ε.den / ε.num.toNat ≤ δ.den / δ.num.toNat
  apply nat_div_le_div_of_cross hεtoNat hδtoNat
  rw [Nat.mul_comm ε.den δ.num.toNat, Nat.mul_comm δ.den ε.num.toNat]
  exact hnatcross

/-! ## 2. Lemma A — stage-parametrized modulus bound `r^N·H ≤ ε` -/

/-- **Lemma A.** For `k ≥ 2`, `0 ≤ H ≤ 1`, and `invSucc N ≤ ε`, the geometric
factor `r^N·H` (`r = 1/k^4`) is `≤ ε`.  Chain:
`r^N·H ≤ half^N·H ≤ half^N·1 = half^N ≤ invSucc N ≤ ε`. -/
theorem ratioPow_mul_H_le_stage {k : Nat} (hk : 2 ≤ k) (H : Q')
    (hH0 : (0 : Q') ≤ H) (hH1 : H ≤ (1 : Q')) (N : Nat) (ε : Q')
    (hNε : Q'.invSucc N ≤ ε) :
    (Pi.ratio k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk)) ^ N * H ≤ ε := by
  have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk
  have hhN_nn : (0 : Q') ≤ HalfPow.half ^ N :=
    Q'.pow_nonneg _ HalfPow.half_nonneg N
  have step1 : (Pi.ratio k hk0) ^ N * H ≤ HalfPow.half ^ N * H :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (Pi.ratio_pow_antitone_half hk N) hH0
  have step2 : HalfPow.half ^ N * H ≤ HalfPow.half ^ N * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hH1 hhN_nn
  have step2' : HalfPow.half ^ N * 1 ≤ HalfPow.half ^ N :=
    Q'.le_of_eqv (Q'.mul_one_eqv _)
  have step3 : HalfPow.half ^ N ≤ Q'.invSucc N := HalfPow.pow_half_le_invSucc N
  exact Q'.le_trans' _ _ _ step1
    (Q'.le_trans' _ _ _ step2
      (Q'.le_trans' _ _ _ step2' (Q'.le_trans' _ _ _ step3 hNε)))

/-! ## 3. Lemma B — stage-parametrized directional Cauchy of `cPart` -/

/-- **Lemma B.** The two-sided Cauchy property of the arctan partial sums
`cPart k` at an arbitrary stage `N`, given the modulus hypothesis `r^N·H ≤ ε`. -/
theorem cPart_cauchy_stage {k : Nat} (hk0 : 0 < k) (H : Q') (hH0 : (0 : Q') ≤ H)
    (hrec : Pi.etaMax k hk0 + Pi.ratio k hk0 * H ≤ H)
    (N : Nat) (ε : Q') (hε : (0 : Q') < ε)
    (hmod : (Pi.ratio k hk0) ^ N * H ≤ ε) :
    ∀ m n, N ≤ m → N ≤ n →
      Pi.cPart k hk0 m ≤ Pi.cPart k hk0 n + ε
        ∧ Pi.cPart k hk0 n ≤ Pi.cPart k hk0 m + ε := by
  have dir : ∀ p q : Nat, N ≤ p → p ≤ q →
      Pi.cPart k hk0 q ≤ Pi.cPart k hk0 p + ε
        ∧ Pi.cPart k hk0 p ≤ Pi.cPart k hk0 q + ε := by
    intro p q hp hpq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
    refine ⟨?_, ?_⟩
    · have hblock := Pi.cPart_block hk0 H hH0 hrec p d
      have hrp_le_rN : (Pi.ratio k hk0) ^ p ≤ (Pi.ratio k hk0) ^ N :=
        Pi.ratioPow_antitone hk0 hp
      have hrp_H_le : (Pi.ratio k hk0) ^ p * H ≤ (Pi.ratio k hk0) ^ N * H :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hrp_le_rN hH0
      have htail : (Pi.ratio k hk0) ^ p * H ≤ ε :=
        Q'.le_trans' _ _ _ hrp_H_le hmod
      exact Q'.le_trans' _ _ _ hblock (Q'.add_le_add_left _ _ _ htail)
    · have hmono : Pi.cPart k hk0 p ≤ Pi.cPart k hk0 (p + d) :=
        Pi.cPart_mono k hk0 (Nat.le_add_right p d)
      exact Q'.le_trans' _ _ _ hmono
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε))
  intro m n hm hn
  rcases Nat.le_total m n with hmn | hnm
  · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
  · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

/-! ## 4. Assembly — the concrete `At5Modulus` datum -/

/-- **The concrete antitone Cauchy modulus for `at5`.**  Discharges the
`ArctanSeriesTrigBridge.At5Modulus` residual with a genuine, non-vacuous datum
(`Mw = atMw = ⌊1/·⌋`). -/
def at5Modulus : ArctanSeriesTrigBridge.At5Modulus where
  Mw := atMw
  hMw := by
    intro ε hε m n hm hn
    rw [Pi.at5_approx m, Pi.at5_approx n]
    exact cPart_cauchy_stage (k := 5) (by decide) (Q'.mkPos 1 4 (by decide))
      (by decide) (by decide) (atMw ε) ε hε
      (ratioPow_mul_H_le_stage (k := 5) (by decide) (Q'.mkPos 1 4 (by decide))
        (by decide) (by decide) (atMw ε) ε (atMw_invSucc_le ε hε))
      m n hm hn
  hMwmono := atMw_antitone

/-! ## 5. Bridge objects at the now-concrete modulus (sole residual:
`ArctanTrigConverges`) -/

/-- `sinC(arctan(1/5))` at the concrete modulus. -/
def sinCat5 : CReal := ArctanSeriesTrigBridge.sinCat5 at5Modulus

/-- `cosC(arctan(1/5))` at the concrete modulus. -/
def cosCat5 : CReal := ArctanSeriesTrigBridge.cosCat5 at5Modulus

/-- **The single remaining honest atom** (transcendental cross-series
convergence), re-exported at the concrete modulus for downstream reference. -/
abbrev ArctanTrigConverges : Prop := ArctanSeriesTrigBridge.ArctanTrigConverges

/-- **Target A (sine) at the concrete modulus.**  `sval ≃ sinCat5`, conditional
ONLY on `ArctanTrigConverges` (the modulus residual is now discharged). -/
theorem sval_eqv_sinCat5 (h : ArctanTrigConverges) :
    CReal.Equiv QDivArctanSeries.sval sinCat5 :=
  ArctanSeriesTrigBridge.sval_eqv_sinCat5 at5Modulus h

/-- **Target A (cosine) at the concrete modulus.**  `cval ≃ cosCat5`. -/
theorem cval_eqv_cosCat5 (h : ArctanTrigConverges) :
    CReal.Equiv QDivArctanSeries.cval cosCat5 :=
  ArctanSeriesTrigBridge.cval_eqv_cosCat5 at5Modulus h

/-- **The tangent identity at the concrete modulus.**
`sinC(arctan(1/5)) ≃ (1/5)·cosC(arctan(1/5))`, conditional ONLY on
`ArctanTrigConverges`. -/
theorem tanLink_at5 (h : ArctanTrigConverges) :
    CReal.Equiv sinCat5
      (CReal.mul (CReal.ofQ' QDivArctanSeries.xv) cosCat5) :=
  ArctanSeriesTrigBridge.tanLink_arctan_fifth_trig at5Modulus h

end YMGap.Continuum.ArctanTrigConverges

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ArctanTrigConverges.atMw_invSucc_le
#print axioms YMGap.Continuum.ArctanTrigConverges.atMw_antitone
#print axioms YMGap.Continuum.ArctanTrigConverges.ratioPow_mul_H_le_stage
#print axioms YMGap.Continuum.ArctanTrigConverges.cPart_cauchy_stage
#print axioms YMGap.Continuum.ArctanTrigConverges.at5Modulus
#print axioms YMGap.Continuum.ArctanTrigConverges.sval_eqv_sinCat5
#print axioms YMGap.Continuum.ArctanTrigConverges.cval_eqv_cosCat5
#print axioms YMGap.Continuum.ArctanTrigConverges.tanLink_at5
