/-
`FusedFreeSplit` — Milestone 14.2, first half: the EXACT free/interacting
split of the blocked channel — the cancellation that `FusedAmpAnchors`
machine-proved to be mandatory, constructed.

# The identity

For `1 ≤ s ≤ N`, the blocked (p = 2 fused) channel coefficient splits
EXACTLY as

    boxSum w N s  ≃  2·coeffW w s  +  intBlock w N s,

where the FREE part `2·coeffW w s` collects the two vacuum pairings
`(0, s)` and `(s, 0)` (one fused factor trivial — no interaction; the `2`
is the free multiplicity the ratio normalization will cancel), and the
INTERACTING block `intBlock` collects every pair with BOTH spins `≥ 1`.
The interacting block carries exponent `≥ 6` (`C₄(a)+C₄(b) ≥ 3+3` for
`a, b ≥ 1`): `intBlock w N s ≤ intAmp N s · w⁶` — three orders of decay
beyond the leading channel weight.  This is the defect identity's first
half: the deviation-from-free of the blocked coefficient is an explicit
exact object with derived amplitude and strictly higher decay.

# What is delivered (all PROVED, axiom-clean)

  * `fsum_peel` — bottom-index peel `Σ_{i<n+1} f = f 0 + Σ_{i<n} f (i+1)`;
  * `fsum_zero_of_bounded` / `delta_fsum` — vanishing-prefix and
    delta-collapse sum lemmas;
  * `fusionInd_zero_left` / `fusionInd_zero_right` — the vacuum fusion
    rows: `0 ⊗ b ∋ s` iff `b = s` (the ladder pins `k = 0`);
  * `intBlock` / `intAmp` — the interacting block and its derived
    amplitude (exact double character sums over spins `≥ 1`);
  * **`boxSum_free_split`** — the exact split (the headline identity);
  * **`intBlock_le`** — the interacting decay `intBlock ≤ intAmp·w⁶` on
    `w ∈ [0, 1]`.

# What remains open (AGENTS.md Rule 6)

The second half of 14.2: the RATIO normalization (blocked channel over
blocked vacuum vs free ratio) where the `2·coeffW w s` free parts cancel
and the residual defect inherits `intBlock`'s amplitudes — then the
`Σ ≤ 6` budget check against `intAmp`.  No frontier type is touched; the
Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusedChannelAll

namespace YMGap.Continuum.FusedFreeSplit

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.FusedChannelOne
open YMGap.Continuum.FusedChannelAll
open YMGap.Continuum.TaylorModel

/-! ## 1. Sum plumbing: bottom peel, bounded vanishing, delta collapse -/

/-- Bottom-index peel: `Σ_{i<n+1} f i ≃ f 0 + Σ_{i<n} f (i+1)`. -/
theorem fsum_peel (f : Nat → Q') :
    ∀ n, (fsum f (n + 1)).eqv (f 0 + fsum (fun i => f (i + 1)) n)
  | 0 => by
      show ((0 : Q') + f 0).eqv (f 0 + 0)
      rw [Q'.zero_add', Q'.add_zero']
      exact Q'.eqv_refl _
  | n + 1 => by
      show (fsum f (n + 1) + f (n + 1)).eqv
        (f 0 + (fsum (fun i => f (i + 1)) n + f (n + 1)))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (fsum_peel f n)) ?_
      exact Q'.add_assoc_eqv (f 0) (fsum (fun i => f (i + 1)) n) (f (n + 1))

/-- A sum whose entries all vanish (up to `eqv`) below the bound vanishes. -/
theorem fsum_zero_of_bounded {f : Nat → Q'} :
    ∀ n, (∀ i, i < n → (f i).eqv 0) → (fsum f n).eqv 0
  | 0, _ => Q'.eqv_refl 0
  | n + 1, h => by
      show (fsum f n + f n).eqv 0
      refine Q'.eqv_trans _ _ _
        (add_eqv_congr_both'
          (fsum_zero_of_bounded n (fun i hi => h i (Nat.lt_succ_of_lt hi)))
          (h n (Nat.lt_succ_self n))) ?_
      rw [Q'.zero_add']
      exact Q'.eqv_refl _

/-- Delta collapse: `Σ_{b<n} (if b = s then 1 else 0)·g b ≃ g s` when
`s < n`. -/
theorem delta_fsum (g : Nat → Q') (s : Nat) :
    ∀ n, s < n →
      (fsum (fun b => (if b = s then (1 : Q') else 0) * g b) n).eqv (g s)
  | 0, h => absurd h (Nat.not_lt_zero s)
  | n + 1, h => by
      show (fsum (fun b => (if b = s then (1 : Q') else 0) * g b) n
          + (if n = s then (1 : Q') else 0) * g n).eqv (g s)
      by_cases hns : n = s
      · -- the head is the delta; the prefix vanishes (all indices < n = s)
        subst hns
        rw [if_pos rfl]
        refine Q'.eqv_trans _ _ _
          (add_eqv_congr_both'
            (fsum_zero_of_bounded n (fun i hi => by
              rw [if_neg (Nat.ne_of_lt hi)]
              exact Q'.zero_mul_eqv (g i)))
            (Q'.one_mul_eqv (g n))) ?_
        rw [Q'.zero_add']
        exact Q'.eqv_refl _
      · -- the delta lives strictly below `n`
        have hs : s < n := by omega
        rw [if_neg hns]
        refine Q'.eqv_trans _ _ _
          (add_eqv_congr_both'
            (delta_fsum g s n hs) (Q'.zero_mul_eqv (g n))) ?_
        rw [Q'.add_zero']
        exact Q'.eqv_refl _

/-! ## 2. The vacuum fusion rows -/

/-- `0 ⊗ b ∋ s` iff `b = s` (the ladder pins `k = 0`). -/
theorem fusionInd_zero_left (b s : Nat) :
    fusionInd 0 b s = (if b = s then (1 : Q') else 0) := by
  unfold fusionInd
  by_cases hbs : b = s
  · subst hbs
    rw [if_pos rfl, if_pos ?_]
    exact (fusionOK_iff_ladder 0 b b).mpr ⟨0, Nat.le_refl 0, Nat.zero_le b,
      by omega⟩
  · rw [if_neg hbs, if_neg ?_]
    intro h
    obtain ⟨k, hk0, _, he⟩ := (fusionOK_iff_ladder 0 b s).mp h
    exact hbs (by omega)

/-- `a ⊗ 0 ∋ s` iff `a = s`. -/
theorem fusionInd_zero_right (a s : Nat) :
    fusionInd a 0 s = (if a = s then (1 : Q') else 0) := by
  unfold fusionInd
  by_cases has : a = s
  · subst has
    rw [if_pos rfl, if_pos ?_]
    exact (fusionOK_iff_ladder a 0 a).mpr ⟨0, Nat.zero_le a, Nat.le_refl 0,
      by omega⟩
  · rw [if_neg has, if_neg ?_]
    intro h
    obtain ⟨k, _, hk0, he⟩ := (fusionOK_iff_ladder a 0 s).mp h
    exact has (by omega)

/-! ## 3. The interacting block and its derived amplitude -/

/-- The interacting block: all pairs with BOTH spins `≥ 1`. -/
def intBlock (w : Q') (N s : Nat) : Q' :=
  fsum (fun a => fsum (fun b =>
    fusionInd (a + 1) (b + 1) s
      * (coeffW w (a + 1) * coeffW w (b + 1))) N) N

/-- The interacting amplitude (exact character sum over spins `≥ 1`). -/
def intAmp (N s : Nat) : Q' :=
  fsum (fun a => fsum (fun b =>
    fusionInd (a + 1) (b + 1) s
      * (dimQ (a + 1) * dimQ (b + 1))) N) N

/-- Termwise `fsum` additivity (local): `Σ (f + g) ≃ Σ f + Σ g`. -/
theorem fsum_add' (f g : Nat → Q') :
    ∀ n, (fsum (fun i => f i + g i) n).eqv (fsum f n + fsum g n)
  | 0 => by
      show (0 : Q').eqv ((0 : Q') + 0)
      rw [Q'.zero_add']
      exact Q'.eqv_refl _
  | n + 1 => by
      show (fsum (fun i => f i + g i) n + (f n + g n)).eqv
        ((fsum f n + f n) + (fsum g n + g n))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (fsum_add' f g n)) ?_
      exact Q'.eqv_symm (add2_pair (fsum f n) (f n) (fsum g n) (g n))

/-! ## 4. THE EXACT SPLIT -/

/-- **`boxSum_free_split` (PROVED — the defect identity's first half).**
For `1 ≤ s ≤ N`:

    boxSum w N s  ≃  coeffW w s + (coeffW w s + intBlock w N s)

(the two vacuum pairings `(0,s)` and `(s,0)` each contribute one free
`coeffW w s`; everything else is the interacting block). -/
theorem boxSum_free_split (w : Q') {N s : Nat} (hs1 : 1 ≤ s) (hsN : s ≤ N) :
    (boxSum w N s).eqv
      (coeffW w s + (coeffW w s + intBlock w N s)) := by
  -- the a = 0 row collapses to c_s
  have hrow0 : ∀ b, (fusionInd 0 b s * (coeffW w 0 * coeffW w b)).eqv
      ((if b = s then (1 : Q') else 0) * coeffW w b) := by
    intro b
    rw [fusionInd_zero_left b s, coeffW_zero]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv (coeffW w b))
  -- each a ≥ 1 row's b = 0 head is a shifted delta
  have hhead : ∀ a, (fusionInd (a + 1) 0 s
        * (coeffW w (a + 1) * coeffW w 0)).eqv
      ((if a = s - 1 then (1 : Q') else 0) * coeffW w (a + 1)) := by
    intro a
    rw [fusionInd_zero_right (a + 1) s, coeffW_zero]
    have hiff : (if a + 1 = s then (1 : Q') else 0)
        = (if a = s - 1 then (1 : Q') else 0) := by
      by_cases h : a + 1 = s
      · rw [if_pos h, if_pos (by omega : a = s - 1)]
      · rw [if_neg h, if_neg (by omega : ¬ a = s - 1)]
    rw [hiff]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv (coeffW w (a + 1)))
  unfold boxSum
  -- peel the `a = 0` row
  refine Q'.eqv_trans _ _ _
    (fsum_peel (fun a => fsum (fun b =>
      fusionInd a b s * (coeffW w a * coeffW w b)) (N + 1)) N) ?_
  refine add_eqv_congr_both' ?_ ?_
  · -- Σ_b δ_{b,s}·c_b ≃ c_s
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr' hrow0 (N + 1)) ?_
    exact delta_fsum (fun b => coeffW w b) s (N + 1) (by omega)
  · -- the a ≥ 1 rows: peel each row's b = 0 head, split, collapse
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr' (fun a =>
        fsum_peel (fun b =>
          fusionInd (a + 1) b s * (coeffW w (a + 1) * coeffW w b)) N)
        N) ?_
    refine Q'.eqv_trans _ _ _
      (fsum_add' (fun a =>
        fusionInd (a + 1) 0 s * (coeffW w (a + 1) * coeffW w 0))
        (fun a => fsum (fun b =>
          fusionInd (a + 1) (b + 1) s
            * (coeffW w (a + 1) * coeffW w (b + 1))) N) N) ?_
    refine add_eqv_congr_both' ?_ (Q'.eqv_refl _)
    -- Σ_a δ_{a,s−1}·c_{a+1} ≃ c_s
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr' hhead N) ?_
    refine Q'.eqv_trans _ _ _
      (delta_fsum (fun a => coeffW w (a + 1)) (s - 1) N (by omega)) ?_
    show (coeffW w (s - 1 + 1)).eqv (coeffW w s)
    have hss : s - 1 + 1 = s := by omega
    rw [hss]
    exact Q'.eqv_refl _

/-! ## 5. The interacting decay -/

/-- Every interacting pair carries exponent `≥ 6` (`C₄ ≥ 3` for each spin
`≥ 1`). -/
theorem int_exp_ge {a b s : Nat}
    (h : fusionOK (a + 1) (b + 1) s = true) :
    6 ≤ c4 (a + 1) + c4 (b + 1) := by
  have ha : 3 ≤ c4 (a + 1) := by
    show 3 ≤ (a + 1) * (a + 1 + 2)
    have h1 : 1 ≤ a + 1 := by omega
    have h3 : 3 ≤ a + 1 + 2 := by omega
    calc 3 = 1 * 3 := rfl
      _ ≤ (a + 1) * (a + 1 + 2) := Nat.mul_le_mul h1 h3
  have hb : 3 ≤ c4 (b + 1) := by
    show 3 ≤ (b + 1) * (b + 1 + 2)
    have h1 : 1 ≤ b + 1 := by omega
    have h3 : 3 ≤ b + 1 + 2 := by omega
    calc 3 = 1 * 3 := rfl
      _ ≤ (b + 1) * (b + 1 + 2) := Nat.mul_le_mul h1 h3
  omega

/-- The interacting per-pair bound at exponent 6. -/
theorem int_pair_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (a b s : Nat) :
    fusionInd (a + 1) (b + 1) s
        * (coeffW w (a + 1) * coeffW w (b + 1))
      ≤ (fusionInd (a + 1) (b + 1) s
          * (dimQ (a + 1) * dimQ (b + 1))) * qpow w 6 := by
  by_cases h : fusionOK (a + 1) (b + 1) s = true
  · have hind : fusionInd (a + 1) (b + 1) s = (1 : Q') := by
      unfold fusionInd
      rw [h]
      rfl
    rw [hind]
    have hexp := int_exp_ge h
    have hcw : (coeffW w (a + 1) * coeffW w (b + 1)).eqv
        ((dimQ (a + 1) * dimQ (b + 1))
          * qpow w (c4 (a + 1) + c4 (b + 1))) := by
      show ((dimQ (a + 1) * qpow w (c4 (a + 1)))
          * (dimQ (b + 1) * qpow w (c4 (b + 1)))).eqv
        ((dimQ (a + 1) * dimQ (b + 1))
          * qpow w (c4 (a + 1) + c4 (b + 1)))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (mul_swap' (qpow w (c4 (a + 1))) (dimQ (b + 1))
            (qpow w (c4 (b + 1))))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (qpow_add' w (c4 (a + 1)) (c4 (b + 1))))
    have hdims : (0 : Q') ≤ dimQ (a + 1) * dimQ (b + 1) :=
      Q'.mul_nonneg _ _ (dimQ_nonneg _) (dimQ_nonneg _)
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv _)) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcw) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (qpow_exp_antitone hw0 hw1 hexp) hdims) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.ge_of_eqv (Q'.one_mul_eqv _)) (qpow_nonneg _ hw0 6)
  · have hind : fusionInd (a + 1) (b + 1) s = (0 : Q') := by
      unfold fusionInd
      rw [if_neg (fun hh => h hh)]
    rw [hind]
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.zero_mul_eqv _)) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_refl' 0) ?_
    exact Q'.ge_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
      (Q'.zero_mul_eqv (qpow w 6)))

/-- **`intBlock_le` (PROVED — the interacting decay).**
`intBlock w N s ≤ intAmp N s · w⁶` on `w ∈ [0, 1]` — three orders beyond
the leading channel weight. -/
theorem intBlock_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N s : Nat) : intBlock w N s ≤ intAmp N s * qpow w 6 := by
  unfold intBlock
  refine Q'.le_trans' _ _ _
    (fsum_le_fsum'
      (fun a => fsum_le_fsum'
        (fun b => int_pair_le hw0 hw1 a b s) N) N) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr'
      (fun a => fsum_factor
        (fun b => fusionInd (a + 1) (b + 1) s
          * (dimQ (a + 1) * dimQ (b + 1)))
        (qpow w 6) N)
      N) ?_
  exact fsum_factor
    (fun a => fsum (fun b =>
      fusionInd (a + 1) (b + 1) s
        * (dimQ (a + 1) * dimQ (b + 1))) N)
    (qpow w 6) N

end YMGap.Continuum.FusedFreeSplit

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusedFreeSplit.fsum_peel
#print axioms YMGap.Continuum.FusedFreeSplit.fsum_zero_of_bounded
#print axioms YMGap.Continuum.FusedFreeSplit.delta_fsum
#print axioms YMGap.Continuum.FusedFreeSplit.fusionInd_zero_left
#print axioms YMGap.Continuum.FusedFreeSplit.fusionInd_zero_right
#print axioms YMGap.Continuum.FusedFreeSplit.fsum_add'
#print axioms YMGap.Continuum.FusedFreeSplit.boxSum_free_split
#print axioms YMGap.Continuum.FusedFreeSplit.int_exp_ge
#print axioms YMGap.Continuum.FusedFreeSplit.int_pair_le
#print axioms YMGap.Continuum.FusedFreeSplit.intBlock_le
