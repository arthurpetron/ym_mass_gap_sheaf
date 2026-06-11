/-
The Kotecký–Preiss infinite-volume limit ENGINE: turning a geometric
increment bound (the analytic output of a convergent cluster expansion)
into a `CReal` limit with an EXPLICIT Cauchy modulus.

# The mathematics

In the convergent (high-β / small-activity) regime, the finite-volume
expectations `⟨o⟩_Λ` form a Cauchy sequence in the volume `Λ` whose
modulus is controlled by the KP cluster-expansion convergence: the
increment `⟨o⟩_{Λ+1} − ⟨o⟩_Λ` is dominated by a geometric tail
`C·ρ^Λ` in the polymer activities (`0 ≤ ρ < 1`).  The infinite-volume
limit `⟨o⟩_∞ = lim_Λ ⟨o⟩_Λ` then EXISTS as a `CReal` with a computable
modulus.

This module isolates the *engine* of that step at the level of `Q'`
partial sums (which is exactly what `RationalTail.finSum` produces), in
two layers:

  1. **`crealOfTail`** — the clean reusable abstraction.  Given a `Q'`
     sequence `S` together with a *tail-bound family* `T : Nat → Q'`
     satisfying a two-sided telescoped bound `S (n+d)` within `T n` of
     `S n` for every gap `d`, plus a modulus `T n → 0`, package `S` as a
     `CReal` whose `approx = S`.  This is the Bishop-regular-Cauchy
     repackaging: the two-sided telescoped tail bound is *exactly* the
     `CReal.cauchy` field, so no regularity surgery is needed.

  2. **The geometric instantiation** — `geoTail`, `geoTail_series_le`,
     `telescope_up`/`telescope_lo`, `geoTail_modulus`, and
     `crealOfGeoIncrement`.  From a two-sided
     SINGLE-STEP geometric increment bound
     `S (Λ+1)` within `C·(1/2)^Λ` of `S Λ`, derive the telescoped tail
     `T n = 2·C·(1/2)^n` (`geometric_tail_closure` for the geometric
     series sum `Σ (1/2)^i ≤ 2`), whose modulus is `HalfPow.pow_half_le`
     (the explicit `(1/2)^k → 0` modulus).  Conclude `S` is a `CReal`.

`ρ = 1/2` is the concrete decay rate carried here (it is the only one
for which the repo already has an explicit `pow → 0` modulus, `HalfPow`).
The KP smallness `Z_t < 1/16` (`Constructive/SU3CharFactor.lean`) provides
the activity bound `ρ < 1`; bridging a general rational `ρ < 1` to a
`pow → 0` modulus is the one missing rational lemma (see the OPEN list in
`docs/kp-limit-notes.md`).  Any `ρ ≤ 1/2` is already covered by domination.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` only, plus `Quot.sound` where `Nat`/`omega` enter via the
reused `Q'`/`finSum` helpers.  No `Classical.*`, no `sorryAx`, no `sorry`,
no `native_decide`.  The Cauchy `∃ N` witness is BHK-constructed (the
modulus `N` is produced explicitly), Rule-8 compatible.
-/

import YMGap.Constructive.Reals
import YMGap.Constructive.GeometricTail
import YMGap.Constructive.CharacterTail
import YMGap.Constructive.HalfPow
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.ExpNeg

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.HalfPow

/-! ## Layer 1 — the reusable abstraction `crealOfTail`

A `Q'` sequence `S` with a two-sided telescoped tail bound and a
modulus is a `CReal`.  The two-sided telescoped tail bound is precisely
the `CReal.cauchy` field written with the gap `d = m − n` made explicit. -/

/-- **Cauchy-from-tail engine (abstract form).**

Given:
  * `S : Nat → Q'` — the partial sums (finite-volume expectations);
  * `T : Nat → Q'` — the tail-bound family (`T n` bounds the total
    movement of `S` from index `n` onward);
  * `hup  : ∀ n d, S (n + d) ≤ S n + T n` — upper telescoped bound;
  * `hlo  : ∀ n d, S n ≤ S (n + d) + T n` — lower telescoped bound;
  * `hmod : ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → T n ≤ ε` — the modulus
    (`T n → 0`),

package `S` as a `CReal` with `approx = S`.  The Cauchy `∃ N` is
discharged by `hmod`, and for `m, n ≥ N` the two-sided bound `T (min) ≤ ε`
plus the telescoped hypotheses give `S m ≤ S n + ε` (both directions). -/
def crealOfTail (S T : Nat → Q')
    (hup : ∀ n d, S (n + d) ≤ S n + T n)
    (hlo : ∀ n d, S n ≤ S (n + d) + T n)
    (hmod : ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → T n ≤ ε) :
    CReal where
  approx := S
  cauchy := by
    intro ε hε
    obtain ⟨N, hN⟩ := hmod ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    constructor
    · -- S m ≤ S n + ε
      rcases Nat.le_total n m with hnm | hmn
      · -- n ≤ m : write m = n + d, use hup at n, T n ≤ ε
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
        exact Q'.le_trans' _ _ _ (hup n d)
          (Q'.add_le_add_left (S n) (T n) ε (hN n hn))
      · -- m ≤ n : write n = m + d, use hlo at m, T m ≤ ε
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact Q'.le_trans' _ _ _ (hlo m d)
          (Q'.add_le_add_left (S (m + d)) (T m) ε (hN m hm))
    · -- S n ≤ S m + ε  (symmetric)
      rcases Nat.le_total m n with hmn | hnm
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact Q'.le_trans' _ _ _ (hup m d)
          (Q'.add_le_add_left (S m) (T m) ε (hN m hm))
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
        exact Q'.le_trans' _ _ _ (hlo n d)
          (Q'.add_le_add_left (S (n + d)) (T n) ε (hN n hn))

@[simp] theorem crealOfTail_approx (S T : Nat → Q')
    (hup : ∀ n d, S (n + d) ≤ S n + T n)
    (hlo : ∀ n d, S n ≤ S (n + d) + T n)
    (hmod : ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → T n ≤ ε)
    (k : Nat) :
    (crealOfTail S T hup hlo hmod).approx k = S k := rfl

/-! ## A general `Q'.pow` addition law

`q^(a+b) ≃ q^a · q^b`.  (`SU3CharFactor.lean` has a private copy; we
re-prove it here so this module is standalone.) -/

namespace Q'

/-- `q^(a+b) ≃ q^a · q^b`. -/
theorem pow_add_eqv (q : Q') (a b : Nat) : (q ^ (a + b)).eqv (q ^ a * q ^ b) := by
  induction b with
  | zero => exact Q'.eqv_symm (Q'.mul_one_eqv (q ^ a))
  | succ b ih =>
    show (q ^ (a + b + 1)).eqv (q ^ a * q ^ (b + 1))
    rw [Q'.pow_succ, Q'.pow_succ]
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left q _ _ ih) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv q (q ^ a) (q ^ b))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (q ^ b) (Q'.mul_comm_eqv q (q ^ a))) ?_
    exact Q'.mul_assoc_eqv (q ^ a) q (q ^ b)

end Q'

/-! ## Layer 2 — the geometric (ρ = 1/2) instantiation

We now manufacture the telescoped tail `T n` and the modulus from a
two-sided SINGLE-STEP geometric increment bound, and feed them to
`crealOfTail`. -/

/-- The geometric tail-bound family `T n = 2·C·(1/2)^n`.  It dominates the
total movement of `S` from index `n` onward when each single step moves
`S` by at most `C·(1/2)^Λ`. -/
def geoTail (C : Q') (n : Nat) : Q' := (Q'.ofNat 2 * C) * half ^ n

theorem geoTail_nonneg (C : Q') (hC : (0 : Q') ≤ C) (n : Nat) :
    (0 : Q') ≤ geoTail C n :=
  Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hC)
    (Q'.pow_nonneg half half_nonneg n)

/-! ### The shifted geometric series sum is `≤ 2·(1/2)^n·C`

The increment at index `n + i` is `C·(1/2)^(n+i) ≃ (C·(1/2)^n)·(1/2)^i`.
Summing over `i < d` and dominating the geometric series `Σ (1/2)^i ≤ 2`
gives `finSum (a ∘ (n+·)) d ≤ 2·(C·(1/2)^n) = geoTail C n`. -/

/-- The single-step increment majorant `a Λ = C·(1/2)^Λ`. -/
def geoIncr (C : Q') (l : Nat) : Q' := C * half ^ l

theorem geoIncr_nonneg (C : Q') (hC : (0 : Q') ≤ C) (l : Nat) :
    (0 : Q') ≤ geoIncr C l :=
  Q'.mul_nonneg _ _ hC (Q'.pow_nonneg half half_nonneg l)

/-- The shifted increment factors: `geoIncr C (n+i) ≃ (C·(1/2)^n)·(1/2)^i`. -/
theorem geoIncr_shift_eqv (C : Q') (n i : Nat) :
    (geoIncr C (n + i)).eqv ((C * half ^ n) * half ^ i) := by
  show (C * half ^ (n + i)).eqv ((C * half ^ n) * half ^ i)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left C (half ^ (n + i)) (half ^ n * half ^ i)
      (Q'.pow_add_eqv half n i)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv C (half ^ n) (half ^ i))

/-- The pure geometric series `Σ_{i<d} K·(1/2)^i ≤ 2·K` for `K ≥ 0`,
via `geom_series_le` with `f0 = K`, `r = 1/2`, `H = 2·K`
(recurrence `K + (1/2)(2K) = 2K ≤ 2K`). -/
theorem geom_half_series_le (K : Q') (hK : (0 : Q') ≤ K) (d : Nat) :
    finSum (fun i => K * half ^ i) d ≤ Q'.ofNat 2 * K := by
  refine CharacterTail.geom_series_le (fun i => K * half ^ i) K half (Q'.ofNat 2 * K)
    half_nonneg (Q'.mul_nonneg _ _ (by decide) hK) ?_ ?_ ?_ d
  · -- f 0 = K·(1/2)^0 = K·1 ≤ K
    show K * half ^ 0 ≤ K
    exact Q'.le_of_eqv (Q'.mul_one_eqv K)
  · -- f (k+1) = K·(1/2)^(k+1) ≤ (1/2)·(K·(1/2)^k)
    intro k
    show K * half ^ (k + 1) ≤ half * (K * half ^ k)
    refine Q'.le_of_eqv ?_
    -- K·(half·half^k) ≃ half·(K·half^k)
    show (K * (half * half ^ k)).eqv (half * (K * half ^ k))
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv K half (half ^ k))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ (half * K) (half ^ k) (Q'.mul_comm_eqv K half)) ?_
    exact Q'.mul_assoc_eqv half K (half ^ k)
  · -- recurrence: K + (1/2)·(2·K) ≤ 2·K
    -- (1/2)·(2·K) ≃ K, so LHS ≃ K + K, and K + K ≤ 2·K (in fact ≃).
    show K + half * (Q'.ofNat 2 * K) ≤ Q'.ofNat 2 * K
    have e1 : (half * (Q'.ofNat 2 * K)).eqv K := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half (Q'.ofNat 2) K)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ (1 : Q') K ?_) (Q'.one_mul_eqv K)
      -- half · 2 ≃ 1
      show (half * Q'.ofNat 2).eqv (1 : Q')
      decide
    -- 2·K ≃ K + K  : 2·K ≃ (1+1)·K ≃ 1·K + 1·K ≃ K + K
    have e2 : (Q'.ofNat 2 * K).eqv (K + K) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 2) ((1 : Q') + 1) K (by decide)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 : Q') 1 K) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((1 : Q') * K) K ((1 : Q') * K) (Q'.one_mul_eqv K)) ?_
      exact Q'.add_eqv_congr_left K ((1 : Q') * K) K (Q'.one_mul_eqv K)
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left K _ K (Q'.le_of_eqv e1)) ?_
    exact Q'.ge_of_eqv e2

/-- **The telescoped tail bound.**  The geometric increments from index `n`
onward sum under `geoTail C n = 2·C·(1/2)^n`:
`finSum (fun i => geoIncr C (n+i)) d ≤ geoTail C n`. -/
theorem geoTail_series_le (C : Q') (hC : (0 : Q') ≤ C) (n d : Nat) :
    finSum (fun i => geoIncr C (n + i)) d ≤ geoTail C n := by
  -- termwise: geoIncr C (n+i) ≃ (C·(1/2)^n)·(1/2)^i
  have hterm : (finSum (fun i => geoIncr C (n + i)) d).eqv
      (finSum (fun i => (C * half ^ n) * half ^ i) d) :=
    RationalTail.finSum_eqv_congr _ _ (fun i => geoIncr_shift_eqv C n i) d
  have hKnn : (0 : Q') ≤ C * half ^ n := Q'.mul_nonneg _ _ hC (Q'.pow_nonneg half half_nonneg n)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hterm) ?_
  refine Q'.le_trans' _ _ _ (geom_half_series_le (C * half ^ n) hKnn d) ?_
  -- 2·(C·(1/2)^n) ≃ (2·C)·(1/2)^n = geoTail C n
  refine Q'.le_of_eqv ?_
  show (Q'.ofNat 2 * (C * half ^ n)).eqv ((Q'.ofNat 2 * C) * half ^ n)
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) C (half ^ n))

/-! ### The two-sided telescoped bound from single-step increments

From `S (Λ+1) ≤ S Λ + geoIncr C Λ` (and the reverse), the telescoped
`S (n+d) ≤ S n + finSum (a ∘ (n+·)) d ≤ S n + geoTail C n`. -/

/-- Upper telescoped bound: `S (n+d) ≤ S n + finSum (a ∘ (n+·)) d`, by
induction on `d` from the single-step upper bound. -/
theorem telescope_up (S a : Nat → Q')
    (hstep : ∀ l, S (l + 1) ≤ S l + a l) (n : Nat) :
    ∀ d, S (n + d) ≤ S n + finSum (fun i => a (n + i)) d
  | 0 => by
    show S n ≤ S n + (0 : Q')
    rw [Q'.add_zero']
    exact Q'.le_refl' (S n)
  | d + 1 => by
    -- S (n+d+1) ≤ S (n+d) + a (n+d) ≤ (S n + Σ_d) + a (n+d) = S n + (Σ_d + a (n+d))
    have ih := telescope_up S a hstep n d
    have hstp : S (n + d + 1) ≤ S (n + d) + a (n + d) := hstep (n + d)
    show S (n + (d + 1)) ≤ S n + (finSum (fun i => a (n + i)) d + a (n + d))
    have e : n + (d + 1) = (n + d) + 1 := by omega
    rw [e]
    refine Q'.le_trans' _ _ _ hstp ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (a (n + d)) ih) ?_
    exact Q'.le_of_eqv (Q'.add_assoc_eqv (S n) (finSum (fun i => a (n + i)) d) (a (n + d)))

/-- Lower telescoped bound: `S n ≤ S (n+d) + finSum (a ∘ (n+·)) d`, by
induction on `d` from the single-step lower bound. -/
theorem telescope_lo (S a : Nat → Q')
    (hstep : ∀ l, S l ≤ S (l + 1) + a l) (n : Nat) :
    ∀ d, S n ≤ S (n + d) + finSum (fun i => a (n + i)) d
  | 0 => by
    show S n ≤ S n + (0 : Q')
    rw [Q'.add_zero']
    exact Q'.le_refl' (S n)
  | d + 1 => by
    -- S n ≤ S (n+d) + Σ_d ≤ (S (n+d+1) + a (n+d)) + Σ_d = S (n+d+1) + (Σ_d + a (n+d))
    have ih := telescope_lo S a hstep n d
    have hstp : S (n + d) ≤ S (n + d + 1) + a (n + d) := hstep (n + d)
    show S n ≤ S (n + (d + 1)) + (finSum (fun i => a (n + i)) d + a (n + d))
    have e : n + (d + 1) = (n + d) + 1 := by omega
    rw [e]
    refine Q'.le_trans' _ _ _ ih ?_
    -- S (n+d) + Σ_d ≤ (S (n+d+1) + a (n+d)) + Σ_d
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (finSum (fun i => a (n + i)) d) hstp) ?_
    -- (S(n+d+1) + a(n+d)) + Σ_d ≃ S(n+d+1) + (a(n+d) + Σ_d) ≃ S(n+d+1) + (Σ_d + a(n+d))
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (S (n + d + 1)) (a (n + d)) (finSum (fun i => a (n + i)) d)) ?_
    exact Q'.add_eqv_congr_left (S (n + d + 1)) _ _
      (Q'.add_comm_eqv (a (n + d)) (finSum (fun i => a (n + i)) d))

/-! ### The geometric modulus `geoTail C n → 0`

`geoTail C n = (2C)·(1/2)^n`.  For target `ε`, choose `n` so that
`(1/2)^n ≤ ε/(2C)` — but to stay inside the repo's `HalfPow` modulus
(which gives `(1/2)^(δ.den) ≤ δ`), we dominate `geoTail C n ≤ (1/2)^(n')`
once `2C ≤ 1` is folded in, OR present the modulus pointwise.  We give the
clean general statement: for any positive `ε`, there is `N` past which
`geoTail C n ≤ ε`, using `pow_half_le` at the rescaled tolerance. -/

/-- `(1/2)^(n+1) ≤ (1/2)^n` (one extra half only shrinks the power). -/
theorem half_pow_le_succ (n : Nat) : half ^ (n + 1) ≤ half ^ n := by
  show half * half ^ n ≤ half ^ n
  -- half·h ≤ 1·h = h since half ≤ 1, h ≥ 0
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right half 1 (half ^ n) (by decide)
      (Q'.pow_nonneg half half_nonneg n)) ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv (half ^ n))

/-- `(1/2)^(m+d) ≤ (1/2)^m` for every offset `d` (induction on `d`). -/
theorem half_pow_add_le (m : Nat) : ∀ d, half ^ (m + d) ≤ half ^ m
  | 0 => Q'.le_refl' _
  | d + 1 => by
    have e : m + (d + 1) = (m + d) + 1 := by omega
    rw [e]
    exact Q'.le_trans' _ _ _ (half_pow_le_succ (m + d)) (half_pow_add_le m d)

/-- `(1/2)^n` is antitone in `n`: `m ≤ n → (1/2)^n ≤ (1/2)^m`. -/
theorem half_pow_antitone (m n : Nat) (h : m ≤ n) : half ^ n ≤ half ^ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact half_pow_add_le m d

/-- **The geometric modulus.**  For positive `ε`, `geoTail C n ≤ ε` for
all `n ≥ N` with an EXPLICIT `N = (ε')` derived from `HalfPow.pow_half_le`
at the rescaled tolerance `ε' = ε/(2C)` — but to avoid `Q'` division we
take the modulus stage where `(2C)·(1/2)^n ≤ ε` holds via
`(1/2)^n ≤ (1/2)^N ≤ ε'` with `ε'·(2C) ≤ ε`.  We package the rescaling as
a hypothesis `hscale : (Q'.ofNat 2 * C) * δ ≤ ε` with `δ` the HalfPow
witness; the canonical instance supplies it by `decide` at concrete data. -/
theorem geoTail_modulus (C : Q') (hC : (0 : Q') ≤ C)
    (ε : Q') (_hε : (0 : Q') < ε)
    (δ : Q') (hδ : (0 : Q') < δ)
    (hscale : (Q'.ofNat 2 * C) * δ ≤ ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → geoTail C n ≤ ε := by
  refine ⟨δ.den, fun n hn => ?_⟩
  -- (1/2)^n ≤ (1/2)^(δ.den) ≤ δ
  have hpow : half ^ n ≤ δ :=
    Q'.le_trans' _ _ _ (half_pow_antitone δ.den n hn) (pow_half_le δ hδ)
  -- geoTail C n = (2C)·(1/2)^n ≤ (2C)·δ ≤ ε
  have h2Cnn : (0 : Q') ≤ Q'.ofNat 2 * C := Q'.mul_nonneg _ _ (by decide) hC
  show (Q'.ofNat 2 * C) * half ^ n ≤ ε
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (half ^ n) δ (Q'.ofNat 2 * C) hpow h2Cnn)
    hscale

/-! ## The capstone: `CReal` limit from a geometric increment bound -/

/-- **Infinite-volume limit from a geometric increment (the KP engine).**

Given a `Q'` partial-sum sequence `S` (the finite-volume expectations)
with a two-sided SINGLE-STEP geometric increment bound

    S (Λ+1) ≤ S Λ + C·(1/2)^Λ   and   S Λ ≤ S (Λ+1) + C·(1/2)^Λ,

together with a rescaling witness `hscale` certifying the `HalfPow`
modulus closes the target tolerance (supplied by `decide` at concrete
`C`), the sequence `S` is Cauchy and defines a `CReal` `⟨o⟩_∞` whose
`approx` is `S` itself.  This is the engine that converts KP geometric
smallness into an infinite-volume limit with an explicit modulus. -/
def crealOfGeoIncrement (S : Nat → Q') (C : Q') (hC : (0 : Q') ≤ C)
    (hup : ∀ l, S (l + 1) ≤ S l + geoIncr C l)
    (hlo : ∀ l, S l ≤ S (l + 1) + geoIncr C l)
    (modulus : ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * C) * δ ≤ ε) :
    CReal :=
  crealOfTail S (geoTail C)
    (fun n d => Q'.le_trans' _ _ _
      (telescope_up S (geoIncr C) hup n d)
      (Q'.add_le_add_left (S n) _ (geoTail C n) (geoTail_series_le C hC n d)))
    (fun n d => Q'.le_trans' _ _ _
      (telescope_lo S (geoIncr C) hlo n d)
      (Q'.add_le_add_left (S (n + d)) _ (geoTail C n) (geoTail_series_le C hC n d)))
    (fun ε hε => by
      obtain ⟨δ, hδ, hscale⟩ := modulus ε hε
      exact geoTail_modulus C hC ε hε δ hδ hscale)

@[simp] theorem crealOfGeoIncrement_approx (S : Nat → Q') (C : Q') (hC : (0 : Q') ≤ C)
    (hup : ∀ l, S (l + 1) ≤ S l + geoIncr C l)
    (hlo : ∀ l, S l ≤ S (l + 1) + geoIncr C l)
    (modulus : ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * C) * δ ≤ ε)
    (k : Nat) :
    (crealOfGeoIncrement S C hC hup hlo modulus).approx k = S k := rfl

/-! ## Target #2 — a concrete convergent polymer sum and its limit

The cleanest concrete instance: the geometric activity sum
`S Λ = Σ_{l<Λ} (1/2)^l` (decay rate `ρ = 1/2 < 1`, the KP-style
small-activity regime).  Its single-step increment is exactly the
activity `S (Λ+1) − S Λ = (1/2)^Λ = geoIncr 1 Λ` (both directions,
since the increment is nonnegative), so `crealOfGeoIncrement` applies
with `C = 1` and the modulus `δ = ε/2` (here `2·C·δ = 2·δ = ε`).  The
limit `geoPolymerLimit` is a genuine `CReal` whose `approx Λ` is the
finite-volume partial sum, with the explicit Cauchy modulus inherited
from `HalfPow.pow_half_le`.  (The exact limit value is `2`, but we only
need — and only claim — its EXISTENCE as a `CReal` with modulus.) -/

/-- The geometric-activity partial sums `S Λ = Σ_{l<Λ} (1/2)^l`. -/
def geoPolymerSum (Λ : Nat) : Q' := finSum (fun l => half ^ l) Λ

/-- The single-step increment is exactly the activity `(1/2)^Λ`. -/
theorem geoPolymerSum_succ (Λ : Nat) :
    geoPolymerSum (Λ + 1) = geoPolymerSum Λ + half ^ Λ := rfl

/-- **A convergent polymer sum has a `CReal` infinite-volume limit with
explicit modulus.**  Instantiation of the KP engine at the geometric
activity `(1/2)^Λ` (`C = 1`): the partial sums `Σ_{l<Λ} (1/2)^l` form a
`CReal`. -/
def geoPolymerLimit : CReal :=
  crealOfGeoIncrement geoPolymerSum 1 Q'.zero_le_one
    (fun l => by
      -- S (l+1) = S l + (1/2)^l ≤ S l + geoIncr 1 l = S l + 1·(1/2)^l
      rw [geoPolymerSum_succ]
      refine Q'.add_le_add_left (geoPolymerSum l) (half ^ l) (geoIncr 1 l) ?_
      show half ^ l ≤ 1 * half ^ l
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv (half ^ l))))
    (fun l => by
      -- S l ≤ S (l+1) + geoIncr 1 l  (since S l ≤ S(l+1) ≤ S(l+1)+nonneg)
      rw [geoPolymerSum_succ]
      refine Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg (geoPolymerSum l) (half ^ l)
          (Q'.pow_nonneg half half_nonneg l)) ?_
      exact Q'.add_le_self_of_nonneg (geoPolymerSum l + half ^ l) (geoIncr 1 l)
        (geoIncr_nonneg 1 Q'.zero_le_one l))
    (fun ε hε => by
      -- δ = ε/2 (half · ε):  2·1·(half·ε) = ε.  Positivity of half·ε from hε.
      refine ⟨half * ε, ExpNeg.half_mul_pos ε hε, ?_⟩
      -- (2·1)·(half·ε) ≤ ε.  Show ≃ ε then le_of_eqv.
      show (Q'.ofNat 2 * 1) * (half * ε) ≤ ε
      refine Q'.le_of_eqv ?_
      -- (2·1)·(half·ε) ≃ 2·(half·ε) ≃ (2·half)·ε ≃ 1·ε ≃ ε
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 2 * 1) (Q'.ofNat 2) (half * ε)
          (Q'.mul_one_eqv (Q'.ofNat 2))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) half ε)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 2 * half) (1 : Q') ε (by decide)) ?_
      exact Q'.one_mul_eqv ε)

/-- The limit's `Λ`-th approximation is exactly the finite-volume partial
sum `Σ_{l<Λ} (1/2)^l` — the infinite-volume limit is genuinely the
`Λ → ∞` limit of the finite-volume expectations. -/
@[simp] theorem geoPolymerLimit_approx (Λ : Nat) :
    geoPolymerLimit.approx Λ = geoPolymerSum Λ := rfl

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.crealOfTail
#print axioms YMGap.Continuum.crealOfTail_approx
#print axioms YMGap.Continuum.Q'.pow_add_eqv
#print axioms YMGap.Continuum.geoTail_nonneg
#print axioms YMGap.Continuum.geoIncr_nonneg
#print axioms YMGap.Continuum.geoIncr_shift_eqv
#print axioms YMGap.Continuum.geom_half_series_le
#print axioms YMGap.Continuum.geoTail_series_le
#print axioms YMGap.Continuum.telescope_up
#print axioms YMGap.Continuum.telescope_lo
#print axioms YMGap.Continuum.half_pow_le_succ
#print axioms YMGap.Continuum.half_pow_add_le
#print axioms YMGap.Continuum.half_pow_antitone
#print axioms YMGap.Continuum.geoTail_modulus
#print axioms YMGap.Continuum.crealOfGeoIncrement
#print axioms YMGap.Continuum.crealOfGeoIncrement_approx
#print axioms YMGap.Continuum.geoPolymerSum
#print axioms YMGap.Continuum.geoPolymerSum_succ
#print axioms YMGap.Continuum.geoPolymerLimit
#print axioms YMGap.Continuum.geoPolymerLimit_approx
