/-
Track A / R2 — the TRUNCATED w-free coupling Turán `(‡_trunc)`, uniform-in-`s`.

# What this module adds (read first — load-bearing honesty)

The full-range coupling Turán `(‡)` (`FusionUTuranEnvelope.uturan_unconditional`) does NOT close
the fusion-box reserve `(†)`: the numerator `acN(s+1,s+1)` uses the FIXED truncation range
`p < s+1`, dropping its top antidiagonal term, so `(‡)`'s RHS bounds a strictly larger quantity
(see `docs/reindexing-correction-2026-07-06.md`).  The correct target is the TRUNCATED coupling
Turán

    (‡_trunc)   256·Wtrunc(Q,s,s)·Wtrunc(Q,s,s+2) ≤ 225·Q·Wtrunc(Q,s,s+1)²,   Q ≥ 4, all s,

where `Wtrunc(Q,s,S) = Σ_{i=1}^{s+1} i·(S+2−i)·Q^{i(S+2−i)} = fsum (wterm Q (S+2)) (s+2)` is the
range-`(s+1)` truncation of the coupling sum (`= acN(s+1,S)/w^{f(S)}`, `Q = 1/w²`).

The KEY reuse: for `s ≥ 2` the numerator's central shell (index `(s+3)/2 ≤ s+1`) lies INSIDE the
truncated range, so the SAME central-term lower leg (`loFn`), the SAME denominator upper legs
(`hi2Fn`, `hi4Fn`, via `Wtrunc ≤ Ucoup ≤ hi`), and the SAME reduced scalar closures
(`utle_reduced`) of `FusionUTuranEnvelope` apply verbatim — assembled through `mono_turan`.  The
edge modes `s = 0, 1` (where the truncation clips a central term) are discharged by direct
monomial `qpow` arguments.

# What is PROVED here (axiom-clean)

  * `Wtrunc`, `Wtrunc_nonneg`, `Wtrunc_diag` (`Wtrunc(Q,s,s) = Ucoup(s+2)`), `Wtrunc_le_Ucoup`
    (partial ≤ full) — the truncated coupling and its transfer to the PROVED upper legs.
  * `Wtrunc_lower_even`, `Wtrunc_lower_odd` — the truncated central-term lower legs (`s ≥ 2`).
  * `uturan_trunc_ge2` — `(‡_trunc)` for `s ≥ 2`, via `mono_turan` + the reused legs.
  * `uturan_trunc_s0`, `uturan_trunc_s1` — the two edge modes, direct monomial arguments.
  * `uturan_trunc_unconditional` — `(‡_trunc)` for ALL `s`, `Q ≥ 4`.

# HONESTY — what is NOT closed here

This module proves `(‡_trunc)` as a pure `Q'`/`Nat` inequality on the truncated coupling `Wtrunc`.
It does NOT itself inhabit any guarded Clay-frontier bundle; the `acN ↔ Wtrunc` reindexing that
would carry `(‡_trunc)` to `AutoconvGershgorin.SymMinorGershgorin` is handled separately.  This is
NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `qpow`/`fsum` API and the PROVED `FusionUTuranEnvelope`
legs, structural `fsum` term-extraction, and `omega` on index identities.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext`/`Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.FusionUTuranEnvelope
import YMGap.Continuum.FusionCoreStep
import YMGap.Continuum.BondMovingMoment

namespace YMGap.Continuum.FusionUTuranTrunc

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusionUTuranWFree
open YMGap.Continuum.FusionUTuranEnvelope

/-! ## 1. The truncated coupling `Wtrunc` and its structural facts -/

/-- The `Ucoup`/`Wtrunc` summand `wterm Q m i = i·(m−i)·Q^{i(m−i)}` (definitionally the `Ucoup`
lambda). -/
def wterm (Q : Q') (m i : Nat) : Q' := Q'.ofNat (i * (m - i)) * qpow Q (i * (m - i))

theorem wterm_nonneg {Q : Q'} (hQ : (0 : Q') ≤ Q) (m i : Nat) : (0 : Q') ≤ wterm Q m i :=
  Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ _)

theorem Ucoup_as_wsum (Q : Q') (m : Nat) : Ucoup Q m = fsum (wterm Q m) m := rfl

/-- **`Wtrunc Q s S`** — the range-`(s+1)` truncation of the coupling sum at total degree `S+2`:
`Σ_{i=1}^{s+1} i·(S+2−i)·Q^{i(S+2−i)} = fsum (wterm Q (S+2)) (s+2)`. -/
def Wtrunc (Q : Q') (s S : Nat) : Q' := fsum (wterm Q (S + 2)) (s + 2)

theorem Wtrunc_nonneg {Q : Q'} (hQ : (0 : Q') ≤ Q) (s S : Nat) : (0 : Q') ≤ Wtrunc Q s S :=
  fsum_nonneg (fun i => wterm_nonneg hQ (S + 2) i) (s + 2)

/-- `Wtrunc(Q,s,s) = Ucoup(s+2)` exactly (range `= s+2 =` degree, no truncation). -/
theorem Wtrunc_diag (Q : Q') (s : Nat) : Wtrunc Q s s = Ucoup Q (s + 2) := rfl

/-- Monotone extension of a nonnegative finite sum: `fsum g a ≤ fsum g b` for `a ≤ b`. -/
theorem fsum_le_extend {g : Nat → Q'} (hg : ∀ i, (0 : Q') ≤ g i) {a b : Nat} (hab : a ≤ b) :
    fsum g a ≤ fsum g b := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hab
  have hsplit := FusionCoreStepRoundH.fsum_split_at g a d
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hsplit)
  exact Q'.add_le_self_of_nonneg (fsum g a) _ (fsum_nonneg (fun r => hg (a + r)) d)

/-- **`Wtrunc_le_Ucoup`** — the truncated sum is bounded by the full coupling `Ucoup(S+2)`;
this transfers the PROVED upper legs (`Ucoup(S+2) ≤ hi`) to `Wtrunc` for free. -/
theorem Wtrunc_le_Ucoup {Q : Q'} (hQ : (0 : Q') ≤ Q) (s S : Nat) (hsS : s ≤ S) :
    Wtrunc Q s S ≤ Ucoup Q (S + 2) := by
  rw [Ucoup_as_wsum]
  exact fsum_le_extend (fun i => wterm_nonneg hQ (S + 2) i) (by omega : s + 2 ≤ S + 2)

/-! ## 2. The truncated central-term LOWER legs (`s ≥ 2`) -/

/-- **`Wtrunc_lower_even`** — for `s = 2t` (`t ≥ 1`), the two central terms of the odd numerator
degree `s+3 = 2t+3` sit at `i = t+1, t+2 ≤ s+1`, so `loFn` transfers to the truncated sum. -/
theorem Wtrunc_lower_even {Q : Q'} (hQ : (0 : Q') ≤ Q) {t : Nat} (ht : 1 ≤ t) :
    loFn Q (2 * t) ≤ Wtrunc Q (2 * t) (2 * t + 1) := by
  rw [loFn_even]
  show (Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2))
        + Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2)))
      ≤ fsum (wterm Q (2 * t + 3)) (2 * t + 2)
  have hi1 : wterm Q (2 * t + 3) (t + 1)
      = Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2)) := by
    unfold wterm
    have he : (t + 1) * (2 * t + 3 - (t + 1)) = (t + 1) * (t + 2) := by
      have : 2 * t + 3 - (t + 1) = t + 2 := by omega
      rw [this]
    rw [he]
  have hi2 : wterm Q (2 * t + 3) (t + 2)
      = Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2)) := by
    unfold wterm
    have he : (t + 2) * (2 * t + 3 - (t + 2)) = (t + 1) * (t + 2) := by
      have : 2 * t + 3 - (t + 2) = t + 1 := by omega
      rw [this]; exact Nat.mul_comm (t + 2) (t + 1)
    rw [he]
  have hkey : wterm Q (2 * t + 3) (t + 1) + wterm Q (2 * t + 3) (t + 2)
      ≤ fsum (wterm Q (2 * t + 3)) (2 * t + 2) :=
    EigShiftOrder.fsum_two_term_le (wterm_nonneg hQ (2 * t + 3)) (t + 1) (t + 2)
      (by omega) (2 * t + 2) (by omega)
  rw [hi1, hi2] at hkey
  exact hkey

/-- **`Wtrunc_lower_odd`** — for `s = 2t+1` (`t ≥ 1`), central + first pair of the even numerator
degree `s+3 = 2t+4` sit at `i = t+1, t+2, t+3 ≤ s+1`, so `loFn` transfers to the truncated sum. -/
theorem Wtrunc_lower_odd {Q : Q'} (hQ : (0 : Q') ≤ Q) {t : Nat} (ht : 1 ≤ t) :
    loFn Q (2 * t + 1) ≤ Wtrunc Q (2 * t + 1) (2 * t + 2) := by
  rw [loFn_odd]
  show (Q'.ofNat ((t + 2) * (t + 2)) * qpow Q ((t + 2) * (t + 2))
      + (Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3))
         + Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3))))
      ≤ fsum (wterm Q (2 * t + 4)) (2 * t + 3)
  have hc : wterm Q (2 * t + 4) (t + 2)
      = Q'.ofNat ((t + 2) * (t + 2)) * qpow Q ((t + 2) * (t + 2)) := by
    unfold wterm
    have he : (t + 2) * (2 * t + 4 - (t + 2)) = (t + 2) * (t + 2) := by
      have : 2 * t + 4 - (t + 2) = t + 2 := by omega
      rw [this]
    rw [he]
  have hp1 : wterm Q (2 * t + 4) (t + 1)
      = Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3)) := by
    unfold wterm
    have he : (t + 1) * (2 * t + 4 - (t + 1)) = (t + 1) * (t + 3) := by
      have : 2 * t + 4 - (t + 1) = t + 3 := by omega
      rw [this]
    rw [he]
  have hp3 : wterm Q (2 * t + 4) (t + 3)
      = Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3)) := by
    unfold wterm
    have he : (t + 3) * (2 * t + 4 - (t + 3)) = (t + 1) * (t + 3) := by
      have : 2 * t + 4 - (t + 3) = t + 1 := by omega
      rw [this]; exact Nat.mul_comm (t + 3) (t + 1)
    rw [he]
  have h3 : (wterm Q (2 * t + 4) (t + 1) + wterm Q (2 * t + 4) (t + 2))
              + wterm Q (2 * t + 4) (t + 3)
      ≤ fsum (wterm Q (2 * t + 4)) (2 * t + 3) :=
    WHMarginTailClose.fsum_three_term_le (wterm_nonneg hQ (2 * t + 4)) (t + 1) (t + 2) (t + 3)
      (by omega) (by omega) (2 * t + 3) (by omega)
  rw [hc, hp1, hp3] at h3
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h3
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)

/-! ## 3. `(‡_trunc)` for `s ≥ 2` — reuse of the PROVED envelope legs via `mono_turan` -/

/-- **`uturan_trunc_ge2`** — the truncated coupling Turán for `s ≥ 2`, `Q ≥ 4`.  Assembled from the
truncated lower leg (numerator), the PROVED upper legs (`Wtrunc ≤ Ucoup ≤ hi`), and the PROVED
reduced scalar closure `utle_reduced`, through the abstract monotone step `mono_turan`. -/
theorem uturan_trunc_ge2 {Q : Q'} (hQ4 : (4 : Q') ≤ Q) {s : Nat} (hs : 2 ≤ s) :
    Q'.ofNat 256 * (Wtrunc Q s s * Wtrunc Q s (s + 2))
      ≤ (Q'.ofNat 225 * Q) * (Wtrunc Q s (s + 1) * Wtrunc Q s (s + 1)) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  -- numerator lower leg (parity split, both need t ≥ 1 ⟸ s ≥ 2)
  have hLA : loFn Q s ≤ Wtrunc Q s (s + 1) := by
    rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
      have ht : 1 ≤ t := by omega
      have := Wtrunc_lower_even hQ0 ht
      -- Wtrunc Q (2t) (2t+1) : the S argument is `2*t+1 = s+1`
      exact this
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      have ht : 1 ≤ t := by omega
      exact Wtrunc_lower_odd hQ0 ht
  -- denominator upper legs
  have hBB' : Wtrunc Q s s ≤ hi2Fn Q s := by
    rw [Wtrunc_diag]; exact utle_upper2 hQ4 s
  have hCC' : Wtrunc Q s (s + 2) ≤ hi4Fn Q s := by
    refine Q'.le_trans' _ _ _ (Wtrunc_le_Ucoup hQ0 s (s + 2) (by omega)) ?_
    exact utle_upper4 hQ4 s
  exact mono_turan (Wtrunc_nonneg hQ0 s (s + 2)) (utle_lo_nonneg hQ4 s) (utle_hi2_nonneg hQ4 s)
    hQ0 hLA hBB' hCC' (utle_reduced hQ4 s)

/-! ## 4. The edge modes `s = 0, 1` — direct monomial arguments -/

open YMGap.Constructive.QPoly

/-- Four-product rearrangement `(a·b)·(c·d) ≃ (a·c)·(b·d)`. -/
private theorem mul4 (a b c d : Q') : ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-- Two monomial blocks multiply into one: `(a·Q^i)·(b·Q^j) ≃ (a·b)·Q^{i+j}`. -/
private theorem blk (Q : Q') (a b i j : Nat) :
    ((Q'.ofNat a * qpow Q i) * (Q'.ofNat b * qpow Q j)).eqv
      (Q'.ofNat (a * b) * qpow Q (i + j)) := by
  refine Q'.eqv_trans _ _ _ (mul4 (Q'.ofNat a) (qpow Q i) (Q'.ofNat b) (qpow Q j)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv a b))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (qpow_add Q i j))

/-- Scale a monomial by a `Nat` constant: `n·(c·Q^k) ≃ (n·c)·Q^k`. -/
private theorem scale (Q : Q') (n c k : Nat) :
    (Q'.ofNat n * (Q'.ofNat c * qpow Q k)).eqv (Q'.ofNat (n * c) * qpow Q k) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n) (Q'.ofNat c) (qpow Q k))) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv n c))

/-- Scale a monomial by `n·Q`: `(n·Q)·(c·Q^k) ≃ (n·c)·Q^{k+1}`. -/
private theorem scaleQ (Q : Q') (n c k : Nat) :
    ((Q'.ofNat n * Q) * (Q'.ofNat c * qpow Q k)).eqv
      (Q'.ofNat (n * c) * qpow Q (k + 1)) := by
  refine Q'.eqv_trans _ _ _ (mul4 (Q'.ofNat n) Q (Q'.ofNat c) (qpow Q k)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv n c))) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  -- Q·Q^k ≃ Q^{k+1}
  show (Q * qpow Q k).eqv (qpow Q (k + 1))
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv Q (qpow Q k)) ?_
  show (qpow Q k * Q).eqv (qpow Q k * Q); exact Q'.eqv_refl _

/-- Combine two equal-power monomials: `a·Q^k + b·Q^k ≃ (a+b)·Q^k`. -/
private theorem combTerm (Q : Q') (a b k : Nat) :
    (Q'.ofNat a * qpow Q k + Q'.ofNat b * qpow Q k).eqv (Q'.ofNat (a + b) * qpow Q k) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat a) (Q'.ofNat b) (qpow Q k))) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (by
    show (Q'.ofNat (a + b)).eqv (Q'.ofNat a + Q'.ofNat b)
    -- ofNat(a+b) ≃ ofNat a + ofNat b
    show ((a + b : Nat) : Int) * (((Q'.ofNat a + Q'.ofNat b).den : Nat) : Int)
        = ((Q'.ofNat a).num * ((Q'.ofNat b).den : Int) + (Q'.ofNat b).num * ((Q'.ofNat a).den : Int))
          * (((Q'.ofNat (a + b)).den : Nat) : Int)
    have h1 : ((Q'.ofNat a + Q'.ofNat b).den : Int) = 1 := rfl
    have h2 : ((Q'.ofNat (a + b)).den : Int) = 1 := rfl
    rw [h1, h2, Int.mul_one, Int.mul_one]
    show ((a + b : Nat) : Int) = (a : Int) * 1 + (b : Int) * 1
    rw [Int.mul_one, Int.mul_one, Int.natCast_add]))

/-- `a·c ≤ b·d` from `a ≤ b`, `c ≤ d`, `0 ≤ c`, `0 ≤ b`. -/
private theorem mulLe {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d) (hc : (0 : Q') ≤ c)
    (hb : (0 : Q') ≤ b) : a * c ≤ b * d :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd hb)

/-- One-power step under `Q ≥ 4`: `a ≤ 4·b ⟹ a·Q^i ≤ b·Q^{i+1}`. -/
private theorem stepQ {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) {a b i : Nat}
    (hab : Q'.ofNat a ≤ Q'.ofNat 4 * Q'.ofNat b) :
    Q'.ofNat a * qpow Q i ≤ Q'.ofNat b * qpow Q (i + 1) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have hqi0 : (0 : Q') ≤ qpow Q i := qpow_nonneg Q hQ0 i
  have hb0 : (0 : Q') ≤ Q'.ofNat b := ofNat_nonneg _
  have h1 : Q'.ofNat a * qpow Q i ≤ (Q'.ofNat 4 * Q'.ofNat b) * qpow Q i :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hab hqi0
  -- (4·b)·Q^i ≃ b·(4·Q^i) ≤ b·(Q·Q^i) = b·Q^{i+1}
  have e1 : ((Q'.ofNat 4 * Q'.ofNat b) * qpow Q i).eqv (Q'.ofNat b * (Q'.ofNat 4 * qpow Q i)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 4) (Q'.ofNat b))) ?_
    exact Q'.mul_assoc_eqv (Q'.ofNat b) (Q'.ofNat 4) (qpow Q i)
  have h4Q : Q'.ofNat 4 * qpow Q i ≤ Q * qpow Q i :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hQ4 hqi0
  have h2 : Q'.ofNat b * (Q'.ofNat 4 * qpow Q i) ≤ Q'.ofNat b * (Q * qpow Q i) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h4Q hb0
  have e2 : (Q'.ofNat b * (Q * qpow Q i)).eqv (Q'.ofNat b * qpow Q (i + 1)) := by
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    show (Q * qpow Q i).eqv (qpow Q i * Q)
    exact Q'.mul_comm_eqv Q (qpow Q i)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv e2)))

/-- The index-0 term of `wterm` vanishes. -/
private theorem wt0 (Q : Q') (m : Nat) : (wterm Q m 0).eqv 0 := by
  show (Q'.ofNat (0 * (m - 0)) * qpow Q (0 * (m - 0))).eqv 0
  have h : 0 * (m - 0) = 0 := by omega
  rw [h]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qpow Q 0) (by decide : (Q'.ofNat 0).eqv 0))
    (q_zero_mul (qpow Q 0))

/-- `fsum (wterm Q m) 2 ≃ wterm Q m 1`. -/
private theorem wtsum2 (Q : Q') (m : Nat) :
    (fsum (wterm Q m) 2).eqv (wterm Q m 1) := by
  show (((0 : Q') + wterm Q m 0) + wterm Q m 1).eqv (wterm Q m 1)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (wterm Q m 1)
      (Q'.eqv_trans _ _ _ (q_zero_add_eqv (wterm Q m 0)) (wt0 Q m))) ?_
  exact q_zero_add_eqv (wterm Q m 1)

/-- `fsum (wterm Q m) 3 ≃ wterm Q m 1 + wterm Q m 2`. -/
private theorem wtsum3 (Q : Q') (m : Nat) :
    (fsum (wterm Q m) 3).eqv (wterm Q m 1 + wterm Q m 2) := by
  show ((((0 : Q') + wterm Q m 0) + wterm Q m 1) + wterm Q m 2).eqv
      (wterm Q m 1 + wterm Q m 2)
  refine Q'.add_eqv_congr_right _ _ (wterm Q m 2) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (wterm Q m 1)
      (Q'.eqv_trans _ _ _ (q_zero_add_eqv (wterm Q m 0)) (wt0 Q m))) ?_
  exact q_zero_add_eqv (wterm Q m 1)

/-- **`uturan_trunc_s0`** — `(‡_trunc)` at `s = 0`.  All three `Wtrunc` are single monomials
(`Q`, `2Q²`, `3Q³`); the inequality is `768·Q⁴ ≤ 900·Q⁵`. -/
theorem uturan_trunc_s0 {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) :
    Q'.ofNat 256 * (Wtrunc Q 0 0 * Wtrunc Q 0 2)
      ≤ (Q'.ofNat 225 * Q) * (Wtrunc Q 0 1 * Wtrunc Q 0 1) := by
  have e00 : (Wtrunc Q 0 0).eqv (Q'.ofNat 1 * qpow Q 1) := wtsum2 Q 2
  have e01 : (Wtrunc Q 0 1).eqv (Q'.ofNat 2 * qpow Q 2) := wtsum2 Q 3
  have e02 : (Wtrunc Q 0 2).eqv (Q'.ofNat 3 * qpow Q 3) := wtsum2 Q 4
  -- LHS ≃ 768·Q⁴
  have hL : (Q'.ofNat 256 * (Wtrunc Q 0 0 * Wtrunc Q 0 2)).eqv (Q'.ofNat 768 * qpow Q 4) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ e00)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ e02) (blk Q 1 3 1 3)))) ?_
    exact scale Q 256 3 4
  -- RHS ≃ 900·Q⁵
  have hR : ((Q'.ofNat 225 * Q) * (Wtrunc Q 0 1 * Wtrunc Q 0 1)).eqv
      (Q'.ofNat 900 * qpow Q 5) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ e01)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ e01) (blk Q 2 2 2 2)))) ?_
    exact scaleQ Q 225 4 4
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hR))
  exact stepQ hQ4 (by decide : Q'.ofNat 768 ≤ Q'.ofNat 4 * Q'.ofNat 900)

/-- **`uturan_trunc_s1`** — `(‡_trunc)` at `s = 1`.  Uses the exact `W11 ≃ 4Q²`, the crude
`W13 ≤ 10Q⁶`, and the single-term lower bound `4Q⁴ ≤ W12`; reduces to `10240·Q⁸ ≤ 3600·Q⁹`. -/
theorem uturan_trunc_s1 {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) :
    Q'.ofNat 256 * (Wtrunc Q 1 1 * Wtrunc Q 1 3)
      ≤ (Q'.ofNat 225 * Q) * (Wtrunc Q 1 2 * Wtrunc Q 1 2) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have hQ1 : (1 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  -- W11 ≃ 2Q² + 2Q²  ⟹  W11 ≤ 4Q²
  have hW11le : Wtrunc Q 1 1 ≤ Q'.ofNat 4 * qpow Q 2 := by
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _ (wtsum3 Q 3) ?_)
    -- wterm Q 3 1 + wterm Q 3 2 = (2·Q²) + (2·Q²) ≃ 4·Q²
    exact combTerm Q 2 2 2
  -- W13 ≃ 4Q⁴ + 6Q⁶  ⟹  W13 ≤ 10Q⁶
  have hW13le : Wtrunc Q 1 3 ≤ Q'.ofNat 10 * qpow Q 6 := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (wtsum3 Q 5)) ?_
    -- (4·Q⁴ + 6·Q⁶) ≤ (4·Q⁶ + 6·Q⁶) ≃ 10·Q⁶
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right (Q'.ofNat 4 * qpow Q 4) (Q'.ofNat 4 * qpow Q 6) (Q'.ofNat 6 * qpow Q 6)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_exp_mono hQ1 (by omega)) (ofNat_nonneg 4))) ?_
    exact Q'.le_of_eqv (combTerm Q 4 6 6)
  -- 4Q⁴ ≤ W12
  have hW12ge : Q'.ofNat 4 * qpow Q 4 ≤ Wtrunc Q 1 2 := by
    show Q'.ofNat 4 * qpow Q 4 ≤ fsum (wterm Q 4) 3
    exact BondMovingMoment.fsum_term_le_of_nonneg (wterm_nonneg hQ0 4) 2 3 (by omega)
  have hW13_0 : (0 : Q') ≤ Wtrunc Q 1 3 := Wtrunc_nonneg hQ0 1 3
  have h4q2_0 : (0 : Q') ≤ Q'.ofNat 4 * qpow Q 2 := Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
  have h4q4_0 : (0 : Q') ≤ Q'.ofNat 4 * qpow Q 4 := Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
  -- LHS ≤ 256·((4Q²)·(10Q⁶)) ≃ 10240·Q⁸
  have hLHS : Q'.ofNat 256 * (Wtrunc Q 1 1 * Wtrunc Q 1 3)
      ≤ Q'.ofNat 10240 * qpow Q 8 := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (mulLe hW11le hW13le hW13_0 h4q2_0) (ofNat_nonneg _)) ?_
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (blk Q 4 10 2 6)) ?_
    exact scale Q 256 40 8
  -- RHS ≥ 225·Q·((4Q⁴)·(4Q⁴)) ≃ 3600·Q⁹
  have hRHS : Q'.ofNat 3600 * qpow Q 9
      ≤ (Q'.ofNat 225 * Q) * (Wtrunc Q 1 2 * Wtrunc Q 1 2) := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (mulLe hW12ge hW12ge h4q4_0 (Wtrunc_nonneg hQ0 1 2))
        (Q'.mul_nonneg _ _ (ofNat_nonneg _) hQ0))
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (blk Q 4 4 4 4)) ?_
    exact scaleQ Q 225 16 8
  refine Q'.le_trans' _ _ _ hLHS (Q'.le_trans' _ _ _ ?_ hRHS)
  exact stepQ hQ4 (by decide : Q'.ofNat 10240 ≤ Q'.ofNat 4 * Q'.ofNat 3600)

/-! ## 5. `(‡_trunc)` UNCONDITIONAL in `s` -/

/-- **`uturan_trunc_unconditional` — the TRUNCATED w-free coupling Turán `(‡_trunc)`, for ALL `s`,
`Q ≥ 4`.**  `256·Wtrunc(Q,s,s)·Wtrunc(Q,s,s+2) ≤ 225·Q·Wtrunc(Q,s,s+1)²`.  Case-split: `s = 0, 1`
by direct monomial argument; `s ≥ 2` by the reused envelope legs through `mono_turan`. -/
theorem uturan_trunc_unconditional {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) (s : Nat) :
    Q'.ofNat 256 * (Wtrunc Q s s * Wtrunc Q s (s + 2))
      ≤ (Q'.ofNat 225 * Q) * (Wtrunc Q s (s + 1) * Wtrunc Q s (s + 1)) := by
  match s with
  | 0 => exact uturan_trunc_s0 hQ4
  | 1 => exact uturan_trunc_s1 hQ4
  | (n + 2) => exact uturan_trunc_ge2 hQ4 (by omega : 2 ≤ n + 2)

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms Wtrunc_nonneg
#print axioms Wtrunc_diag
#print axioms Wtrunc_le_Ucoup
#print axioms Wtrunc_lower_even
#print axioms Wtrunc_lower_odd
#print axioms uturan_trunc_ge2
#print axioms uturan_trunc_s0
#print axioms uturan_trunc_s1
#print axioms uturan_trunc_unconditional

end YMGap.Continuum.FusionUTuranTrunc
