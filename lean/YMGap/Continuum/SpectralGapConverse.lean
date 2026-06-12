/-
Clustering ⇒ gap (the converse), at finite volume.  Milestone F.1 of
`docs/uniform-parametric-bound-plan.md` Part II.

`SpectralGap.lean` folded the *gap ⇒ clustering* direction. This module
folds the physically load-bearing *converse*: measured exponential
clustering `corr S n ≤ C·μ^n` forces a spectral gap — every populated
mode has `λ_j ≤ μ`. This is the finite-volume content of "exponential
decay of the connected two-point function ⇒ a mass gap": the statement
the lattice GEVP effective-mass extraction operationalizes.

The proof is constructive and division-free (`Q'` has no reciprocal):

  1. `term_le_corr` — a single nonnegative spectral term is ≤ the finite
     sum, so `w_j · λ_j^n ≤ corr S n ≤ C·μ^n` for all `n`.
  2. `pow_dominates` — the geometric-growth kernel: if `μ < λ` and
     `w > 0`, then `∃ n, C·μ^n < w·λ^n` (a faster geometric eventually
     overtakes any constant multiple of a slower one). Proved from a
     division-free Bernoulli bound + the `Q'` Archimedean property.
  3. Combine: `μ < λ_j` would give both `C·μ^n < w_j·λ_j^n` and
     `w_j·λ_j^n ≤ C·μ^n` — contradiction. Hence `λ_j ≤ μ`.

Axiom-gate (AGENTS.md Rule 1): every theorem `#print axioms` = `[propext]`
only (via the reused `Q'` order lemmas). No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.SpectralGap

namespace YMGap.Continuum.SpectralGap

open YMGap.Constructive
open YMGap.Constructive.RationalTail

/-! ## `Q'` strict-order helpers

The budget-focused stack never built strict-order theory; these are the
minimal facts the converse needs. All reduce to `Int` and close by
`omega` / `Int` lemmas (treating cross-products as atoms where linear). -/

/-- `0 < q ↔ 0 < q.num` (the denominator is structurally positive). -/
theorem pos_iff_num_pos (q : Q') : (0 : Q') < q ↔ 0 < q.num := by
  show (0 : Int) * (q.den : Int) < q.num * (1 : Int) ↔ (0 : Int) < q.num
  rw [Int.zero_mul, Int.mul_one]

/-- Product of positives is positive. -/
theorem mul_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a * b := by
  rw [pos_iff_num_pos] at ha hb ⊢
  show (0 : Int) < a.num * b.num
  exact Int.mul_pos ha hb

/-- Powers of a positive are positive. -/
theorem pow_pos {q : Q'} (h : (0 : Q') < q) (n : Nat) : (0 : Q') < q ^ n := by
  induction n with
  | zero =>
      show (0 : Q') < 1
      rw [pos_iff_num_pos]; decide
  | succ n ih =>
      show (0 : Q') < q * q ^ n
      exact mul_pos h ih

/-- From `¬ a ≤ b` conclude `b < a` (decidable total order on `Int`). -/
theorem lt_of_not_le {a b : Q'} (h : ¬ a ≤ b) : b < a := by
  have hh : ¬ (a.num * (b.den : Int) ≤ b.num * (a.den : Int)) := h
  exact Int.not_le.mp hh

/-- `a ≤ b` rules out `b < a`. -/
theorem not_lt_of_le {a b : Q'} (h : a ≤ b) : ¬ b < a := by
  have hh : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h
  exact Int.not_lt.mpr hh

/-! ## Single-term domination: a term is ≤ the finite sum -/

/-- A partial sum of nonnegative terms is nonnegative. -/
theorem finSum_nonneg (f : QSeq) (hf : ∀ i, (0 : Q') ≤ f i) (m : Nat) :
    (0 : Q') ≤ finSum f m := by
  have h := finSum_monotone_of_nonneg f hf 0 m (Nat.zero_le m)
  rwa [finSum_zero] at h

/-- Any single nonnegative term is ≤ the finite sum that contains it. -/
theorem finSum_ge_term (f : QSeq) (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ m j, j < m → f j ≤ finSum f m
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | m + 1, j, hj => by
      show f j ≤ finSum f m + f m
      rcases Nat.lt_or_ge j m with hjm | hjm
      · -- j < m : use IH, then add the nonnegative tail term
        have ih := finSum_ge_term f hf m j hjm
        have htail : finSum f m ≤ finSum f m + f m :=
          Q'.add_le_self_of_nonneg (finSum f m) (f m) (hf m)
        exact Q'.le_trans' _ _ _ ih htail
      · -- j ≥ m and j < m+1 ⇒ j = m
        have hjeq : j = m := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) hjm
        subst hjeq
        have h1 : (0 : Q') + f j ≤ finSum f j + f j :=
          Q'.add_le_add_right 0 (finSum f j) (f j) (finSum_nonneg f hf j)
        rw [Q'.zero_add'] at h1
        exact h1

/-- The populated single-mode bound `w_j · λ_j^n ≤ corr S n`. -/
theorem term_le_corr (S : SpectralModel) (n j : Nat) (hj : j < S.k) :
    S.w j * (S.lam j) ^ n ≤ corr S n :=
  finSum_ge_term (fun i => S.w i * (S.lam i) ^ n)
    (fun i => Q'.mul_nonneg (S.w i) ((S.lam i) ^ n)
      (S.w_nonneg i) (Q'.pow_nonneg (S.lam i) (S.lam_nonneg i) n))
    S.k j hj

/-! ## The converse, reduced to the geometric-growth kernel

`DecaysAt S C μ` is measured exponential clustering: `corr S n ≤ C·μ^n`. -/
def DecaysAt (S : SpectralModel) (C μ : Q') : Prop :=
  ∀ n, corr S n ≤ C * μ ^ n

/-- **Clustering ⇒ gap (finite volume), modulo the growth kernel.**

Given the geometric-growth kernel `pow_dominates` (a faster geometric
overtakes any constant multiple of a slower one), measured clustering at
rate `μ` forces every populated mode below `μ`. The kernel is discharged
separately as `pow_dominates` below. -/
theorem gap_of_decay_of_growth
    (S : SpectralModel) (C μ : Q')
    (growth : ∀ (w lam : Q'), (0 : Q') < w → μ < lam →
      ∃ n : Nat, C * μ ^ n < w * lam ^ n)
    (hdecay : DecaysAt S C μ)
    (j : Nat) (hj : j < S.k) (hwj : (0 : Q') < S.w j) :
    S.lam j ≤ μ := by
  by_cases hcon : S.lam j ≤ μ
  · exact hcon
  · exfalso
    have hlt : μ < S.lam j := lt_of_not_le hcon
    obtain ⟨n, hn⟩ := growth (S.w j) (S.lam j) hwj hlt
    have hterm : S.w j * (S.lam j) ^ n ≤ corr S n := term_le_corr S n j hj
    have hle : S.w j * (S.lam j) ^ n ≤ C * μ ^ n :=
      Q'.le_trans' _ _ _ hterm (hdecay n)
    exact (not_lt_of_le hle) hn

/-! ## The remaining kernel (F.1 follow-on)

`gap_of_decay_of_growth` reduces clustering ⇒ gap to the pure-arithmetic
geometric-growth fact

  `pow_dominates : 0 < μ → μ < λ → 0 < w → 0 ≤ C → ∃ n, C·μ^n < w·λ^n`

(a faster geometric eventually overtakes any constant multiple of a
slower one). It is `Q'`-elementary but needs strict-order arithmetic the
budget stack never built: a division-free Bernoulli bound
`λ^(n+1) ≥ μ^(n+1) + (n+1)·μ^n·(λ−μ)` (induction), `Q'` cancellation by a
positive factor, and the `Q'` Archimedean property `∀ X Y, 0<Y → ∃ n,
X < (ofNat n)·Y`. Tracked as a hypothesis-gated obligation in
`lean/SORRY_LEDGER.md` (NOT a `sorry`; this module is axiom-clean).
Discharging it specializes `gap_of_decay_of_growth` to the unconditional
`gap_of_decay` (`Continuum/SpectralGapGrowth.lean`). -/

/-! ## The finite-volume gap ⇔ clustering equivalence

`SpectralGap.decay_of_spectralGap` is the *forward* direction (gap ⇒ decay):
a gap at `μ` forces `corr S n ≤ (Σ_i w_i)·μ^n`.  `gap_of_decay_of_growth` above
is the *converse* (decay ⇒ gap).  Packaging them gives the finite-volume
equivalence — the load-bearing statement that the lattice GEVP effective-mass
extraction operationalizes.

The forward direction is unconditional.  The converse is gated on the
geometric-growth kernel `growth` (a pure `Q'`-arithmetic fact), discharged
unconditionally as `pow_dominates`/`gap_of_decay` in
`Continuum/SpectralGapGrowth.lean`; this module keeps the equivalence in the
kernel-gated form to stay non-circular (the discharge imports *this* module). -/

/-- Spectral gap at `μ`: every mode `≤ μ` (the hypothesis of
`SpectralGap.decay_of_spectralGap`). -/
def HasGapAt (S : SpectralModel) (μ : Q') : Prop := SpectralGapBound S μ

/-- **Gap ⇒ clustering (forward, unconditional).**  A gap at `μ ≥ 0` forces
`corr S n ≤ (Σ_i w_i)·μ^n` — exponential decay at rate `−log μ`.  (Repackaging
of `SpectralGap.decay_of_spectralGap` under the `DecaysAt` envelope, with the
total weight `Σ_i w_i` as the prefactor `C`.) -/
theorem clustering_of_gap (S : SpectralModel) (μ : Q') (hμ : (0 : Q') ≤ μ)
    (hgap : HasGapAt S μ) : DecaysAt S (finSum S.w S.k) μ :=
  fun n => decay_of_spectralGap S μ hμ hgap n

/-- **Finite-volume gap ⇔ clustering (kernel-gated).**

Given the geometric-growth kernel `growth` (discharged unconditionally by
`SpectralGapGrowth.pow_dominates`), the following are equivalent for a
populated mode `j` (`w_j > 0`):

  * a spectral gap at `μ` (every mode `≤ μ`), which forces `λ_j ≤ μ`; and
  * measured exponential clustering `corr S n ≤ C·μ^n`.

Concretely: clustering at rate `μ` ⇒ `λ_j ≤ μ` (the converse), and a gap at `μ`
⇒ clustering with `C = Σ_i w_i` (the forward direction).  This is the
finite-volume content of "exponential decay of the connected two-point
function ⇔ a mass gap". -/
theorem gap_iff_clustering_of_growth
    (S : SpectralModel) (C μ : Q') (hμ : (0 : Q') ≤ μ)
    (growth : ∀ (w lam : Q'), (0 : Q') < w → μ < lam →
      ∃ n : Nat, C * μ ^ n < w * lam ^ n)
    (j : Nat) (hj : j < S.k) (hwj : (0 : Q') < S.w j) :
    (DecaysAt S C μ → S.lam j ≤ μ)
      ∧ (HasGapAt S μ → DecaysAt S (finSum S.w S.k) μ) :=
  ⟨fun hdecay => gap_of_decay_of_growth S C μ growth hdecay j hj hwj,
   fun hgap => clustering_of_gap S μ hμ hgap⟩

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms pos_iff_num_pos
#print axioms mul_pos
#print axioms pow_pos
#print axioms lt_of_not_le
#print axioms not_lt_of_le
#print axioms finSum_nonneg
#print axioms finSum_ge_term
#print axioms term_le_corr
#print axioms gap_of_decay_of_growth
#print axioms clustering_of_gap
#print axioms gap_iff_clustering_of_growth

end YMGap.Continuum.SpectralGap
