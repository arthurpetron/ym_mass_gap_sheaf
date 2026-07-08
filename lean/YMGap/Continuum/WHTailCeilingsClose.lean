/-
Track A / R2 (track: 1-whceilings) — CLOSING the two full-window θ-envelope ceilings
(`WHMarginTailClose.WHTailCeilings`) via the reflect-and-fold sum bound, supplying the one
genuinely missing rational atom — the geometric θ-ceiling `Σ_{i<M} (¼)^{i(i+1)} ≤ 16/15`.

# What this module adds (read first — load-bearing honesty)

`WHMarginTailClose` reduced the entire `WHAllSMargin` frontier to a single named structure
`WHTailCeilings` — the two full-window θ-envelope ceilings

    evenCeil M :  acN wH (2M+1) (2M)   ≤ (151/100)·(c_M·c_M)
    oddCeil  M :  acN wH (2M+2) (2M+1) ≤ (16/15)·(2·c_M·c_{M+1})

with `c_k = coeffW wH k`, `σ = qpow wH 2 = ¼`.  The EVEN θ-atom `theta3_quarter_ceiling`
(`1 + 2·Σ_{i<M} σ^{(i+1)²} ≤ 151/100`) and the two per-term Gaussian window envelopes
(`gWin_even_term_le`, `gWin_odd_term_le`) already exist in `WHAllSMarginTail`.  The ODD side needed
one further rational ceiling that was NOT anywhere in the tree:

    theta_odd_ceiling M :  Σ_{i<M} σ^{i(i+1)}  ≤  16/15.

This module SUPPLIES that atom in full, plus the term-ratio domination `oddGeom_dom` it rests on, and
the reflect-and-fold assembly of both `WHTailCeilings` fields from the θ-atoms and the per-term
envelopes.

DELIVERABLE (PROVED, axiom-clean `Q'`/`Nat` arithmetic):
  * `oddGeom_dom` — the term-ratio domination `σ^{(k+1)(k+2)} ≤ σ² · σ^{k(k+1)}` (exponent
    `(k+1)(k+2) = k(k+1) + (2k+2) ≥ 2 + k(k+1)`).
  * `theta_odd_ceiling` — THE new atom: `Σ_{i<M} σ^{i(i+1)} ≤ 16/15`, uniform in depth `M`.
    Proof: `CharacterTail.geom_series_le` with `f₀ = 1`, ratio `r = σ² = 1/16`, `H = 16/15`; the
    exact recurrence `1 + (1/16)(16/15) = 16/15` closes it by `decide` on closed rationals.
  * the reflect-and-fold sum bounds `evenFold`/`oddFold` and the assembled `whTailCeilings`.

# HONESTY — scope

This module closes the last two full-window θ-envelope ceilings, supplying the one genuinely missing
rational atom (`theta_odd_ceiling`).  Composed with the in-tree
`WHMarginTailClose.whAllSMarginOfCeilings`, an inhabitant of `WHTailCeilings` inhabits the whole
`LaplaceMarginDeep.WHAllSMargin` frontier.  This is a structural sharpening of one box-level
log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`qpow`/`acN`/`gWin`/`fsum`/`finSum` definitions, the
proved per-term Gaussian envelopes, the `CharacterTail` geometric tail bound, `omega` on index
identities, and `decide` only on closed concrete-rational facts.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.WHMarginTailClose
import YMGap.Continuum.CubeRatioBounds
import YMGap.Continuum.FusionCoreStep
import YMGap.Continuum.ChebOrthoOffDiag
import YMGap.Constructive.CharacterTail

namespace YMGap.Continuum.WHTailCeilingsClose

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.LaplaceMarginDeep
open YMGap.Continuum.WHAllSMarginTail
open YMGap.Continuum.WHMarginTailClose
open YMGap.Continuum.MovingCutoff
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.EigShiftOrder

/-! ## 1. The one genuinely missing atom — the geometric θ-ceiling `Σ σ^{i(i+1)} ≤ 16/15` -/

/-- **`oddGeom_dom`** — term-ratio domination: `σ^{(k+1)(k+2)} ≤ σ² · σ^{k(k+1)}`
(exponent `(k+1)(k+2) = k(k+1) + (2k+2) ≥ 2 + k(k+1)`, `σ = qpow wH 2 ∈ [0,1]`). -/
private theorem oddGeom_dom : ∀ k,
    qpow (qpow wH 2) ((k + 1) * ((k + 1) + 1))
      ≤ qpow (qpow wH 2) 2 * qpow (qpow wH 2) (k * (k + 1)) := by
  intro k
  have hσ0 : (0 : Q') ≤ qpow wH 2 := by decide
  have hσ1 : qpow wH 2 ≤ (1 : Q') := by decide
  have hexp : 2 + k * (k + 1) ≤ (k + 1) * ((k + 1) + 1) := by
    have h1 : (k + 1) * ((k + 1) + 1) = (k + 1) * (k + 1) + (k + 1) := Nat.mul_succ (k + 1) (k + 1)
    have h2 : (k + 1) * (k + 1) = k * (k + 1) + (k + 1) := Nat.succ_mul k (k + 1)
    omega
  exact Q'.le_trans' _ _ _
    (qpow_antitone hσ0 hσ1 (2 + k * (k + 1)) ((k + 1) * ((k + 1) + 1)) hexp)
    (Q'.le_of_eqv (qpow_add (qpow wH 2) 2 (k * (k + 1))))

/-- **`theta_odd_ceiling`** — the geometric θ-ceiling `Σ_{i<M} σ^{i(i+1)} ≤ 16/15`.
Peel `i=0` (term `=1`); for `i≥1`, `i(i+1) ≥ 2i` so `σ^{i(i+1)} ≤ (1/16)^i`, and
`Σ_{i≥1}(1/16)^i = 1/15`.  Exact recurrence: `1 + (1/16)(16/15) = 16/15`. -/
theorem theta_odd_ceiling :
    ∀ M, fsum (fun i => qpow (qpow wH 2) (i * (i + 1))) M
          ≤ Q'.mkPos 16 15 (by decide) := by
  intro M
  have hgeom := CharacterTail.geom_series_le
    (fun i => qpow (qpow wH 2) (i * (i + 1)))
    (1 : Q') (qpow (qpow wH 2) 2) (Q'.mkPos 16 15 (by decide))
    (by decide) (by decide)
    (by decide)
    oddGeom_dom
    (by decide) M
  rw [fsum_eq_finSum]
  exact hgeom

/-! ## 2. Small `Q'` helpers (local copies; pure commutative algebra) -/

/-- Sum of two `≤`s. -/
private theorem add_le_add' {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c h1) (Q'.add_le_add_left b c d h2)

/-- `ofNat 2 · z ≃ z + z`. -/
private theorem two_mul_eqv (z : Q') : (Q'.ofNat 2 * z).eqv (z + z) := by
  have h1 : (Q'.ofNat 2 * z).eqv (((1 : Q') + 1) * z) :=
    Q'.mul_eqv_congr_right (Q'.ofNat 2) ((1 : Q') + 1) z (by decide)
  have h2 : (((1 : Q') + 1) * z).eqv ((1 : Q') * z + (1 : Q') * z) :=
    Q'.add_mul_eqv (1 : Q') (1 : Q') z
  have h3 : ((1 : Q') * z + (1 : Q') * z).eqv (z + z) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ ((1 : Q') * z) (Q'.one_mul_eqv z))
      (Q'.add_eqv_congr_left z _ _ (Q'.one_mul_eqv z))
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h3)

/-- `X·(Y·Z) ≃ Y·(X·Z)`. -/
private theorem mul3_swap' (X Y Z : Q') : (X * (Y * Z)).eqv (Y * (X * Z)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv X Y Z))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ Z (Q'.mul_comm_eqv X Y))
      (Q'.mul_assoc_eqv Y X Z))

/-- `gWin` is nonnegative. -/
private theorem gWin_nonneg (N p : Nat) : (0 : Q') ≤ gWin wH N p :=
  Q'.mul_nonneg _ _ (coeffW_nonneg (by decide) p) (coeffW_nonneg (by decide) (N - p))

/-! ## 3. The two block-bound helpers (reversed front / direct tail) -/

/-- **`block_direct`** — a tail block bound: if `F p ≤ σ^{e p}·b` for `p < L`, then
`Σ_{p<L} F p ≤ b·Σ_{k<L} σ^{e k}`. -/
private theorem block_direct (b : Q') (e : Nat → Nat) (F : Nat → Q') (L : Nat)
    (hbound : ∀ p, p < L → F p ≤ qpow (qpow wH 2) (e p) * b) :
    fsum F L ≤ b * fsum (fun k => qpow (qpow wH 2) (e k)) L := by
  have h1 : fsum F L ≤ fsum (fun p => qpow (qpow wH 2) (e p) * b) L :=
    fsum_mono_lt L hbound
  have h2 : (fsum (fun p => qpow (qpow wH 2) (e p) * b) L).eqv
      (b * fsum (fun k => qpow (qpow wH 2) (e k)) L) :=
    Q'.eqv_trans _ _ _
      (fsum_eqv_congr_lt _ (fun k => b * qpow (qpow wH 2) (e k)) L
        (fun _ _ => Q'.mul_comm_eqv _ _))
      (Q'.eqv_symm (fsum_const_mul b (fun k => qpow (qpow wH 2) (e k)) L))
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2)

/-- **`block_reversed`** — a front block bound: if `F p ≤ σ^{e (L−1−p)}·b` for `p < L`, then
`Σ_{p<L} F p ≤ b·Σ_{k<L} σ^{e k}` (the reflection reindex `p ↦ L−1−p`). -/
private theorem block_reversed (b : Q') (e : Nat → Nat) (F : Nat → Q') (L : Nat)
    (hbound : ∀ p, p < L → F p ≤ qpow (qpow wH 2) (e (L - 1 - p)) * b) :
    fsum F L ≤ b * fsum (fun k => qpow (qpow wH 2) (e k)) L := by
  have h1 : fsum F L ≤ fsum (fun p => qpow (qpow wH 2) (e (L - 1 - p)) * b) L :=
    fsum_mono_lt L hbound
  have hrev : (fsum (fun p => qpow (qpow wH 2) (e (L - 1 - p)) * b) L).eqv
      (fsum (fun k => (fun p => qpow (qpow wH 2) (e (L - 1 - p)) * b) (L - 1 - k)) L) := by
    rw [fsum_eq_finSum (fun p => qpow (qpow wH 2) (e (L - 1 - p)) * b) L,
        fsum_eq_finSum (fun k => (fun p => qpow (qpow wH 2) (e (L - 1 - p)) * b) (L - 1 - k)) L]
    exact finSum_reverse (fun p => qpow (qpow wH 2) (e (L - 1 - p)) * b) L
  have hcongr : (fsum (fun k => (fun p => qpow (qpow wH 2) (e (L - 1 - p)) * b) (L - 1 - k)) L).eqv
      (fsum (fun k => qpow (qpow wH 2) (e k) * b) L) := by
    refine fsum_eqv_congr_lt _ _ L (fun k _ => ?_)
    have heq : (fun p => qpow (qpow wH 2) (e (L - 1 - p)) * b) (L - 1 - k)
        = qpow (qpow wH 2) (e k) * b := by
      show qpow (qpow wH 2) (e (L - 1 - (L - 1 - k))) * b = qpow (qpow wH 2) (e k) * b
      rw [show L - 1 - (L - 1 - k) = k from by omega]
    exact Q'.eqv_of_eq heq
  have h3 : (fsum (fun k => qpow (qpow wH 2) (e k) * b) L).eqv
      (b * fsum (fun k => qpow (qpow wH 2) (e k)) L) :=
    Q'.eqv_trans _ _ _
      (fsum_eqv_congr_lt _ (fun k => b * qpow (qpow wH 2) (e k)) L
        (fun _ _ => Q'.mul_comm_eqv _ _))
      (Q'.eqv_symm (fsum_const_mul b (fun k => qpow (qpow wH 2) (e k)) L))
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hrev (Q'.eqv_trans _ _ _ hcongr h3)))

/-! ## 4. The even fold `evenCeil` -/

/-- Reflect-and-fold algebra: `(b·Θ + b) + b·Θ ≃ b·(1 + 2·Θ)` (the even peak-symmetric assembly). -/
private theorem fold_algebra_even (b Θ : Q') :
    ((b * Θ + b) + b * Θ).eqv (b * ((1 : Q') + Q'.ofNat 2 * Θ)) := by
  have e1 : ((b * Θ + b) + b * Θ).eqv ((b + b * Θ) + b * Θ) :=
    Q'.add_eqv_congr_right _ _ (b * Θ) (Q'.add_comm_eqv (b * Θ) b)
  have e2 : ((b + b * Θ) + b * Θ).eqv (b + (b * Θ + b * Θ)) :=
    Q'.add_assoc_eqv b (b * Θ) (b * Θ)
  have e3 : (b + (b * Θ + b * Θ)).eqv (b + Q'.ofNat 2 * (b * Θ)) :=
    Q'.add_eqv_congr_left b _ _ (Q'.eqv_symm (two_mul_eqv (b * Θ)))
  have e4 : (b + Q'.ofNat 2 * (b * Θ)).eqv (b + b * (Q'.ofNat 2 * Θ)) :=
    Q'.add_eqv_congr_left b _ _ (Q'.eqv_symm (mul3_swap' b (Q'.ofNat 2) Θ))
  have e5 : (b + b * (Q'.ofNat 2 * Θ)).eqv (b * 1 + b * (Q'.ofNat 2 * Θ)) :=
    Q'.add_eqv_congr_right _ _ (b * (Q'.ofNat 2 * Θ)) (Q'.eqv_symm (Q'.mul_one_eqv b))
  have e6 : (b * 1 + b * (Q'.ofNat 2 * Θ)).eqv (b * ((1 : Q') + Q'.ofNat 2 * Θ)) :=
    Q'.eqv_symm (Q'.mul_add_eqv b 1 (Q'.ofNat 2 * Θ))
  exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3
    (Q'.eqv_trans _ _ _ e4 (Q'.eqv_trans _ _ _ e5 e6))))

/-- **`evenFold`** — the even full-window θ-envelope ceiling
`acN wH (2M+1) (2M) ≤ (151/100)·(c_M·c_M)`. -/
theorem evenFold (M : Nat) :
    acN wH (2 * M + 1) (2 * M)
      ≤ Q'.mkPos 151 100 (by decide) * (coeffW wH M * coeffW wH M) := by
  have hb0 : (0 : Q') ≤ gWin wH (2 * M) M := gWin_nonneg _ _
  show fsum (fun p => gWin wH (2 * M) p) (2 * M + 1)
      ≤ Q'.mkPos 151 100 (by decide) * (coeffW wH M * coeffW wH M)
  -- front block (reversed), tail block (direct)
  have hfront : fsum (fun p => gWin wH (2 * M) p) M
      ≤ gWin wH (2 * M) M * fsum (fun k => qpow (qpow wH 2) ((k + 1) * (k + 1))) M :=
    block_reversed (gWin wH (2 * M) M) (fun k => (k + 1) * (k + 1))
      (fun p => gWin wH (2 * M) p) M (fun p hp => by
        have hsym := gWin_symm wH (N := 2 * M) (p := p) (by omega)
        have hb := gWin_even_term_le (m := M) (i := M - p) (by omega)
        rw [show M + (M - p) = 2 * M - p from by omega] at hb
        have hchain : gWin wH (2 * M) p
            ≤ qpow (qpow wH 2) ((M - p) * (M - p)) * gWin wH (2 * M) M :=
          Q'.le_trans' _ _ _ (Q'.le_of_eqv hsym) hb
        show gWin wH (2 * M) p
            ≤ qpow (qpow wH 2) (((M - 1 - p) + 1) * ((M - 1 - p) + 1)) * gWin wH (2 * M) M
        rw [show (M - 1 - p) + 1 = M - p from by omega]
        exact hchain)
  have htail : fsum (fun i => gWin wH (2 * M) (M + 1 + i)) M
      ≤ gWin wH (2 * M) M * fsum (fun k => qpow (qpow wH 2) ((k + 1) * (k + 1))) M :=
    block_direct (gWin wH (2 * M) M) (fun k => (k + 1) * (k + 1))
      (fun i => gWin wH (2 * M) (M + 1 + i)) M (fun i hi => by
        have hb := gWin_even_term_le (m := M) (i := i + 1) (by omega)
        rwa [show M + (i + 1) = M + 1 + i from by omega] at hb)
  -- split the window at the peak
  have hsplit := fsum_split_at (fun p => gWin wH (2 * M) p) (M + 1) M
  rw [show (M + 1) + M = 2 * M + 1 from by omega] at hsplit
  have hpeel : fsum (fun p => gWin wH (2 * M) p) (M + 1)
      = fsum (fun p => gWin wH (2 * M) p) M + gWin wH (2 * M) M := rfl
  rw [hpeel] at hsplit
  -- combine
  have hcomb : fsum (fun p => gWin wH (2 * M) p) (2 * M + 1)
      ≤ (gWin wH (2 * M) M * fsum (fun k => qpow (qpow wH 2) ((k + 1) * (k + 1))) M
          + gWin wH (2 * M) M)
        + gWin wH (2 * M) M * fsum (fun k => qpow (qpow wH 2) ((k + 1) * (k + 1))) M :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (add_le_add' (Q'.add_le_add_right _ _ (gWin wH (2 * M) M) hfront) htail)
  -- fold algebra + θ₃ ceiling + commute
  have hbM : gWin wH (2 * M) M = coeffW wH M * coeffW wH M := by
    show coeffW wH M * coeffW wH (2 * M - M) = coeffW wH M * coeffW wH M
    rw [show 2 * M - M = M from by omega]
  refine Q'.le_trans' _ _ _ hcomb ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (fold_algebra_even (gWin wH (2 * M) M)
      (fsum (fun k => qpow (qpow wH 2) ((k + 1) * (k + 1))) M))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (theta3_quarter_ceiling M) hb0) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv (gWin wH (2 * M) M) (Q'.mkPos 151 100 (by decide)))) ?_
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left (Q'.mkPos 151 100 (by decide)) _ _ (Q'.eqv_of_eq hbM))

/-! ## 5. The odd fold `oddCeil` -/

/-- Reflect-and-fold algebra (odd): `b·Θ + b·Θ ≃ ... ≤ (16/15)·(2·b')` handled inline. -/
theorem oddFold (M : Nat) :
    acN wH (2 * M + 2) (2 * M + 1)
      ≤ Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (coeffW wH M * coeffW wH (M + 1))) := by
  have hb0 : (0 : Q') ≤ gWin wH (2 * M + 1) M := gWin_nonneg _ _
  show fsum (fun p => gWin wH (2 * M + 1) p) (2 * M + 2)
      ≤ Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (coeffW wH M * coeffW wH (M + 1)))
  -- front block (reversed) and tail block (direct), each ≤ b·Θodd  (Θodd at depth M+1)
  have hfront : fsum (fun p => gWin wH (2 * M + 1) p) (M + 1)
      ≤ gWin wH (2 * M + 1) M
        * fsum (fun k => qpow (qpow wH 2) (k * (k + 1))) (M + 1) :=
    block_reversed (gWin wH (2 * M + 1) M) (fun k => k * (k + 1))
      (fun p => gWin wH (2 * M + 1) p) (M + 1) (fun p hp => by
        -- p ≤ M ; write p = M - (M - p) and apply the odd envelope with i = M - p
        have hb := gWin_odd_term_le (m := M) (i := M - p) (by omega)
        rw [show M - (M - p) = p from by omega] at hb
        rwa [show (M + 1) - 1 - p = M - p from by omega])
  have htail : fsum (fun i => gWin wH (2 * M + 1) (M + 1 + i)) (M + 1)
      ≤ gWin wH (2 * M + 1) M
        * fsum (fun k => qpow (qpow wH 2) (k * (k + 1))) (M + 1) :=
    block_direct (gWin wH (2 * M + 1) M) (fun k => k * (k + 1))
      (fun i => gWin wH (2 * M + 1) (M + 1 + i)) (M + 1) (fun i hi => by
        have hsym := gWin_symm wH (N := 2 * M + 1) (p := M + 1 + i) (by omega)
        have hb := gWin_odd_term_le (m := M) (i := i) (by omega)
        rw [show 2 * M + 1 - (M + 1 + i) = M - i from by omega] at hsym
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsym) hb)
  -- split at the (no-center) midpoint
  have hsplit := fsum_split_at (fun p => gWin wH (2 * M + 1) p) (M + 1) (M + 1)
  rw [show (M + 1) + (M + 1) = 2 * M + 2 from by omega] at hsplit
  have hcomb : fsum (fun p => gWin wH (2 * M + 1) p) (2 * M + 2)
      ≤ gWin wH (2 * M + 1) M * fsum (fun k => qpow (qpow wH 2) (k * (k + 1))) (M + 1)
        + gWin wH (2 * M + 1) M * fsum (fun k => qpow (qpow wH 2) (k * (k + 1))) (M + 1) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) (add_le_add' hfront htail)
  -- b·Θ + b·Θ ≃ 2·(b·Θ) ; then θodd ceiling and commute to (16/15)·(2·b')
  have hbM : gWin wH (2 * M + 1) M = coeffW wH M * coeffW wH (M + 1) := by
    show coeffW wH M * coeffW wH (2 * M + 1 - M) = coeffW wH M * coeffW wH (M + 1)
    rw [show 2 * M + 1 - M = M + 1 from by omega]
  -- 2·(b·Θ) form
  refine Q'.le_trans' _ _ _ hcomb ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (two_mul_eqv
      (gWin wH (2 * M + 1) M * fsum (fun k => qpow (qpow wH 2) (k * (k + 1))) (M + 1))))) ?_
  -- 2·(b·Θ) ≤ 2·(b·(16/15))
  have hbtheta : gWin wH (2 * M + 1) M * fsum (fun k => qpow (qpow wH 2) (k * (k + 1))) (M + 1)
      ≤ gWin wH (2 * M + 1) M * Q'.mkPos 16 15 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (theta_odd_ceiling (M + 1)) hb0
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hbtheta (by decide)) ?_
  -- 2·(b·(16/15)) ≃ (16/15)·(2·b)
  have hswap : (Q'.ofNat 2 * (gWin wH (2 * M + 1) M * Q'.mkPos 16 15 (by decide))).eqv
      (Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * gWin wH (2 * M + 1) M)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
        (Q'.mul_comm_eqv (gWin wH (2 * M + 1) M) (Q'.mkPos 16 15 (by decide)))) ?_
    exact mul3_swap' (Q'.ofNat 2) (Q'.mkPos 16 15 (by decide)) (gWin wH (2 * M + 1) M)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hswap) ?_
  exact Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.mkPos 16 15 (by decide)) _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (Q'.eqv_of_eq hbM)))

/-! ## 6. The assembled `WHTailCeilings` and the composed `WHAllSMargin` -/

/-- **`whTailCeilings`** — both full-window θ-envelope ceilings, inhabiting the named residual of
`WHMarginTailClose`. -/
def whTailCeilings : WHMarginTailClose.WHTailCeilings where
  evenCeil := evenFold
  oddCeil := oddFold

/-- **`whAllSMargin`** — composing with the in-tree reduction, the two closed ceilings inhabit the
whole `LaplaceMarginDeep.WHAllSMargin` frontier. -/
def whAllSMargin : LaplaceMarginDeep.WHAllSMargin :=
  WHMarginTailClose.whAllSMarginOfCeilings whTailCeilings

/-! ## 7. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `oddGeom_dom`, `theta_odd_ceiling` — the one genuinely missing rational atom `Σ σ^{i(i+1)} ≤ 16/15`.
  * `block_direct`, `block_reversed` — the tail/front block bounds (const-factor + reflection reindex).
  * `evenFold`, `oddFold` — the two full-window θ-envelope ceilings.
  * `whTailCeilings` — INHABITS `WHMarginTailClose.WHTailCeilings` (the previously named-open residual).
  * `whAllSMargin` — composed inhabitant of `LaplaceMarginDeep.WHAllSMargin`.

NAMED OPEN: none in this module — the two ceilings are fully closed here.

HONEST VERDICT.  This module closes the last two full-window θ-envelope ceilings, supplying the one
genuinely missing rational atom.  Composed with the in-tree reduction it inhabits the whole
`WHAllSMargin` frontier.  This is a structural sharpening of one box-level log-concavity sub-fact; it
is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.WHTailCeilingsClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WHTailCeilingsClose.theta_odd_ceiling
#print axioms YMGap.Continuum.WHTailCeilingsClose.evenFold
#print axioms YMGap.Continuum.WHTailCeilingsClose.oddFold
#print axioms YMGap.Continuum.WHTailCeilingsClose.whTailCeilings
#print axioms YMGap.Continuum.WHTailCeilingsClose.whAllSMargin
