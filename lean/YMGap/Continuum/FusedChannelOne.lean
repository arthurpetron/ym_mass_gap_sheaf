/-
`FusedChannelOne` — Milestone 14.1, first deliverable: the `s = 1` fused
channel DERIVED — `FusedDominatedByHK N 1` inhabited with exact rational
amplitude and the FUSED exponent, by character calculus alone.

# The structural finding (map §6, constructive discipline)

For the fused (p = 2) channel sum `boxSum w N s = Σ_{a,b≤N} 1[s ∈ a⊗b]·
c_a·c_b` with `c_a = dimQ a · w^{C₄(a)}`, every contributing pair carries
the exponent `C₄(a) + C₄(b)`, and the channel's decay is governed by the
FUSION-MINIMAL exponent `min_{a⊗b∋s} C₄(a)+C₄(b)` — NOT by the free
`C₄(s)` (fusion ENHANCES high channels: e.g. `(1,1) → s = 2` carries `w⁶`,
slower than the free `w⁸`).  For `s = 1` every fusing pair is a ladder
neighbour pair `{t, t+1}`, the minimal pair is `(0,1)`, and the fused
exponent is `C₄(0) + C₄(1) = 3`.

# What is delivered (all PROVED, axiom-clean)

  * `qpow_exp_antitone` — `n ≤ m → qpow w m ≤ qpow w n` on `w ∈ [0,1]`;
  * `fsum_factor` — `Σ (f i · c) ≃ (Σ f)·c` (the amplitude factorization);
  * `fusionOK_one_exp` — every pair fusing to channel 1 has
    `3 ≤ C₄(a) + C₄(b)` (ladder + convexity, `omega`-level);
  * `fusedAmp1` — the DERIVED amplitude: the exact double character sum
    `Σ_{a,b≤N} 1[1 ∈ a⊗b]·dimQ a·dimQ b` (a computable rational for every
    `N`; no measured number anywhere);
  * **`boxSum_one_le`** — the channel bound
    `boxSum w N 1 ≤ fusedAmp1 N · qpow w 3` for all `w ∈ [0,1]`, all `N`;
  * **`fusedDominated_one`** — `FusedDominatedByHK N 1` INHABITED with the
    derived data (`amp := fusedAmp1 N`, `expn := 3`) — the first channel of
    the 14.1 derivation, done constructively.

# What remains open (AGENTS.md Rule 6)

The general-`s` minimal-pair lemma and the remaining retained channels
(same proof shape; the minimal pair for `s` is `(0, s)` giving
`fusedExp = C₄(s)` only when no interior pair beats it — for `s ≥ 2` the
balanced pairs DO beat it, and the correct exponents must be derived, not
assumed); then 14.2 (the defect identity).  No frontier type is touched;
the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusedAmplitudeDerivation
import YMGap.Continuum.FusionBratteli

namespace YMGap.Continuum.FusedChannelOne

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.TaylorModel
open YMGap.Continuum.TaylorModelStep2

/-! ## 1. Exponent antitonicity and the factorization lemma -/

/-- Exponent additivity for the `RGTransport.qpow` (local). -/
theorem qpow_add' (w : Q') (a : Nat) :
    ∀ b, (qpow w (a + b)).eqv (qpow w a * qpow w b)
  | 0 => by
      show (qpow w a).eqv (qpow w a * 1)
      exact Q'.eqv_symm (Q'.mul_one_eqv (qpow w a))
  | b + 1 => by
      show (qpow w (a + b) * w).eqv (qpow w a * (qpow w b * w))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (qpow_add' w a b)) ?_
      exact Q'.mul_assoc_eqv (qpow w a) (qpow w b) w

/-- `n ≤ m → qpow w m ≤ qpow w n` on `w ∈ [0,1]` (each extra factor
shrinks). -/
theorem qpow_exp_antitone {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    {n m : Nat} (hnm : n ≤ m) : qpow w m ≤ qpow w n := by
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_add' w n d)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (YMGap.Continuum.HeatKernelGap.qpow_le_one hw0 hw1 d)
      (qpow_nonneg _ hw0 n)) ?_
  exact Q'.le_of_eqv (Q'.mul_one_eqv (qpow w n))

/-- Pointwise-`eqv` congruence for `fsum`. -/
theorem fsum_eqv_congr' {f g : Nat → Q'} (h : ∀ i, (f i).eqv (g i)) :
    ∀ n, (fsum f n).eqv (fsum g n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      show (fsum f n + f n).eqv (fsum g n + g n)
      exact add_eqv_congr_both' (fsum_eqv_congr' h n) (h n)

/-- `Σ_{i<n} (f i · c) ≃ (Σ_{i<n} f i)·c`. -/
theorem fsum_factor (f : Nat → Q') (c : Q') :
    ∀ n, (fsum (fun i => f i * c) n).eqv (fsum f n * c)
  | 0 => by
      show (0 : Q').eqv ((0 : Q') * c)
      exact Q'.eqv_symm (Q'.zero_mul_eqv c)
  | n + 1 => by
      show (fsum (fun i => f i * c) n + f n * c).eqv ((fsum f n + f n) * c)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (fsum_factor f c n)) ?_
      exact Q'.eqv_symm (Q'.add_mul_eqv (fsum f n) (f n) c)

/-! ## 2. The fused exponent for channel 1 -/

/-- Every pair fusing to channel `1` carries exponent at least `3`
(`= C₄(0) + C₄(1)`, the minimal pair): the ladder forces `a + b ≥ 1`, so
some member is `≥ 1` and its Casimir alone is `≥ 3`. -/
theorem fusionOK_one_exp {a b : Nat} (h : fusionOK a b 1 = true) :
    3 ≤ c4 a + c4 b := by
  obtain ⟨k, _, _, he⟩ := (fusionOK_iff_ladder a b 1).mp h
  -- a + b = 1 + 2k ≥ 1, so a ≥ 1 or b ≥ 1; c4 x = x(x+2) ≥ 3 for x ≥ 1
  rcases Nat.lt_or_ge a 1 with ha | ha
  · -- `a = 0`, so `b = 1 + 2k ≥ 1`
    have hb : 1 ≤ b := by omega
    have h3 : 3 ≤ c4 b := by
      show 3 ≤ b * (b + 2)
      exact Nat.mul_le_mul hb (Nat.add_le_add hb (Nat.le_refl 2))
    exact Nat.le_trans h3 (Nat.le_add_left _ _)
  · have h3 : 3 ≤ c4 a := by
      show 3 ≤ a * (a + 2)
      exact Nat.mul_le_mul ha (Nat.add_le_add ha (Nat.le_refl 2))
    exact Nat.le_trans h3 (Nat.le_add_right _ _)

/-! ## 3. The derived amplitude and the channel bound -/

/-- **The DERIVED amplitude** for channel 1: the exact double character sum
`Σ_{a,b≤N} 1[1 ∈ a⊗b] · dimQ a · dimQ b` — a computable rational for every
truncation `N`; no measured number. -/
def fusedAmp1 (N : Nat) : Q' :=
  fsum (fun a => fsum (fun b =>
    fusionInd a b 1 * (dimQ a * dimQ b)) (N + 1)) (N + 1)

theorem fusedAmp1_nonneg (N : Nat) : (0 : Q') ≤ fusedAmp1 N :=
  fsum_nonneg
    (fun a => fsum_nonneg
      (fun b => Q'.mul_nonneg _ _ (fusionInd_nonneg a b 1)
        (Q'.mul_nonneg _ _ (dimQ_nonneg a) (dimQ_nonneg b)))
      (N + 1))
    (N + 1)

/-- The per-pair bound: each contributing term is dominated by its
dimension product times the FUSED minimal exponent weight `w³`. -/
theorem pair_term_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (a b : Nat) :
    fusionInd a b 1 * (coeffW w a * coeffW w b)
      ≤ (fusionInd a b 1 * (dimQ a * dimQ b)) * qpow w 3 := by
  by_cases h : fusionOK a b 1 = true
  · -- contributing pair: 1·(cw·cw) ≤ (1·dims)·w³
    have hind : fusionInd a b 1 = (1 : Q') := by
      unfold fusionInd
      rw [h]
      rfl
    rw [hind]
    have hexp := fusionOK_one_exp h
    -- (dA·qA)·(dB·qB) ≃ (dA·dB)·qpow w (C₄a + C₄b)
    have hcw : (coeffW w a * coeffW w b).eqv
        ((dimQ a * dimQ b) * qpow w (c4 a + c4 b)) := by
      show ((dimQ a * qpow w (c4 a)) * (dimQ b * qpow w (c4 b))).eqv
        ((dimQ a * dimQ b) * qpow w (c4 a + c4 b))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (dimQ a) (qpow w (c4 a))
          (dimQ b * qpow w (c4 b))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (mul_swap' (qpow w (c4 a)) (dimQ b) (qpow w (c4 b)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (dimQ a) (dimQ b)
          (qpow w (c4 a) * qpow w (c4 b)))) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (qpow_add' w (c4 a) (c4 b)))
    -- dims·w^{sum} ≤ dims·w³
    have hdims : (0 : Q') ≤ dimQ a * dimQ b :=
      Q'.mul_nonneg _ _ (dimQ_nonneg a) (dimQ_nonneg b)
    have hbound : (dimQ a * dimQ b) * qpow w (c4 a + c4 b)
        ≤ (dimQ a * dimQ b) * qpow w 3 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (qpow_exp_antitone hw0 hw1 hexp) hdims
    -- assemble: 1·(cwa·cwb) ≤ (1·dims)·w³
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv (coeffW w a * coeffW w b))) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcw) ?_
    refine Q'.le_trans' _ _ _ hbound ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.ge_of_eqv (Q'.one_mul_eqv (dimQ a * dimQ b)))
      (qpow_nonneg _ hw0 3)
  · -- non-contributing pair: both sides vanish
    have hind : fusionInd a b 1 = (0 : Q') := by
      unfold fusionInd
      rw [if_neg (fun hh => h hh)]
    rw [hind]
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.zero_mul_eqv (coeffW w a * coeffW w b))) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_refl' 0) ?_
    exact Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.zero_mul_eqv (dimQ a * dimQ b)))
      (Q'.zero_mul_eqv (qpow w 3)))

/-- **`boxSum_one_le` (PROVED — the first DERIVED channel bound).**
`boxSum w N 1 ≤ fusedAmp1 N · w³` for every `w ∈ [0, 1]` and every
truncation `N` — amplitude and exponent both derived from the character
calculus; no measured number. -/
theorem boxSum_one_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) : boxSum w N 1 ≤ fusedAmp1 N * qpow w 3 := by
  unfold boxSum
  -- termwise: each inner sum dominated with the w³ factored per term
  have hterm : fsum (fun a => fsum (fun b =>
      fusionInd a b 1 * (coeffW w a * coeffW w b)) (N + 1)) (N + 1)
      ≤ fsum (fun a => fsum (fun b =>
        (fusionInd a b 1 * (dimQ a * dimQ b)) * qpow w 3) (N + 1)) (N + 1) :=
    fsum_le_fsum'
      (fun a => fsum_le_fsum'
        (fun b => pair_term_le hw0 hw1 a b) (N + 1)) (N + 1)
  refine Q'.le_trans' _ _ _ hterm ?_
  -- factor `w³` out of both sums
  have hfac : (fsum (fun a => fsum (fun b =>
      (fusionInd a b 1 * (dimQ a * dimQ b)) * qpow w 3) (N + 1)) (N + 1)).eqv
      (fusedAmp1 N * qpow w 3) := by
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr'
        (fun a => fsum_factor
          (fun b => fusionInd a b 1 * (dimQ a * dimQ b))
          (qpow w 3) (N + 1))
        (N + 1)) ?_
    exact fsum_factor
      (fun a => fsum (fun b =>
        fusionInd a b 1 * (dimQ a * dimQ b)) (N + 1))
      (qpow w 3) (N + 1)
  exact Q'.le_of_eqv hfac

/-- **`fusedDominated_one` (PROVED — `FusedDominatedByHK N 1` INHABITED
with derived data).**  The first channel of the 14.1 derivation:
amplitude `fusedAmp1 N` (exact character sum), fused exponent `3`. -/
def fusedDominated_one (N : Nat) : FusedDominatedByHK N 1 where
  amp := fusedAmp1 N
  expn := 3
  amp_nonneg := fusedAmp1_nonneg N
  dominates := fun u hu0 hu1 => by
    have hw0 : (0 : Q') ≤ (1 : Q') - u :=
      YMGap.Continuum.HeatKernelChannelTM.one_sub_nonneg hu1
    have hw1 : (1 : Q') - u ≤ 1 :=
      YMGap.Continuum.HeatKernelChannelTM.one_sub_le_one hu0
    exact boxSum_one_le hw0 hw1 N

end YMGap.Continuum.FusedChannelOne

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusedChannelOne.qpow_exp_antitone
#print axioms YMGap.Continuum.FusedChannelOne.fsum_factor
#print axioms YMGap.Continuum.FusedChannelOne.fusionOK_one_exp
#print axioms YMGap.Continuum.FusedChannelOne.fusedAmp1_nonneg
#print axioms YMGap.Continuum.FusedChannelOne.pair_term_le
#print axioms YMGap.Continuum.FusedChannelOne.boxSum_one_le
#print axioms YMGap.Continuum.FusedChannelOne.fusedDominated_one
