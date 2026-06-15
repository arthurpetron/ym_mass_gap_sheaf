/-
SU(N) fundamental-weight Casimir / gap data — the rep-theory foundation of the
uniform character-tail cap (`notes/uniform-character-tail-bound.md` §2a, the
previously-prose "Casimir splits below" step, now Lean for the WHOLE A_{N−1}
family).

# Why this module

The uniform SU(N) tail cap reduces (rank-collapse, `RG/RankCollapse.lean`) to a
sum over the `r = N−1` per-axis character tails, each governed by the
fundamental-weight Casimir `C₂(ω_i)`.  The existing `RepTheory.suN_gap_lb`
covers ONLY the `i = 1` weight (`C₂_fund = (N²−1)/(2N) ≥ 3/4`).  The cap needs
ALL fundamental weights `ω_i`, `1 ≤ i ≤ N−1`.

For A_{N−1} = SU(N), the data has a clean closed form in
`q_i := i(N−i)` (the number of positive roots containing the i-th simple root,
which is ALSO the per-axis multiplicity `n_i`):

  * `C₂(ω_i) = q_i·(N+1)/(2N)`,
  * `‖ω_i‖² = G_ii = q_i/N`,
  * the Casimir split rate `h_i(x) = (q_i/2)·x·(1 + x/N)`  (so `h_i(1) = C₂(ω_i)`).

# What this module PROVES (axiom-clean Q' / Nat)

  * `suN_qWeight_ge` — **`q_i ≥ N−1`**, the rigorous combinatorial fact that the
    per-axis multiplicity is minimized at `i = 1` (and `i = N−1`), value `N−1`.
    Proof: `i(N−i) − (N−1) = (i−1)(N−1−i) ≥ 0`.  This is the precise statement
    that **the `i = 1` axis is the worst case** (largest tail / smallest gap) —
    the SU(N) analogue of "SU(2) is the worst group".
  * `suN_C2_fundweight_gap_lb` — **every SU(N) fundamental weight clears the
    `3/4` gap floor**: `Casimir.gapFloor ≤ C₂(ω_i)` for all `1 ≤ i ≤ N−1`.
    Reduces (via `q_i ≥ N−1`) to the `N² ≥ 2N` nonlinear step of `suN_gap_lb`.

This is the rep-theory layer the cap's majorant rests on, for ALL N.  The
remaining cap obligation (the per-axis exponential tail bounds + the final sum
inequality) is documented in `docs/sun-uniform-cap-factorization.md`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` only (Q' order / Nat).  No `Classical.*`, no `sorryAx`.
-/

import YMGap.RepTheory.SimpleGroup

namespace YMGap.RepTheory

open YMGap.Constructive

/-! ## The per-axis multiplicity `q_i = i(N−i)` and the worst-case fact -/

/-- `q_i = i·(N−i)` for `A_{N−1} = SU(N)`: the number of positive roots
containing the i-th simple root (`= n_i`), and the integer scale of `C₂(ω_i)`. -/
def suN_qWeight (N i : Nat) : Nat := i * (N - i)

/-- **`q_i ≥ N−1` — the `i = 1` axis is the worst case.**  The per-axis
multiplicity `i(N−i)` is minimized at the endpoints `i = 1, N−1` (value `N−1`),
because `i(N−i) − (N−1) = (i−1)(N−1−i) ≥ 0`.  The rigorous SU(N) analogue of
"SU(2) is the worst group". -/
theorem suN_qWeight_ge (N i : Nat) (hi : 1 ≤ i) (hiN : i + 1 ≤ N) :
    N - 1 ≤ suN_qWeight N i := by
  show N - 1 ≤ i * (N - i)
  -- write N = i + j with j = N − i ≥ 1
  obtain ⟨j, rfl, hj1⟩ : ∃ j, N = i + j ∧ 1 ≤ j := ⟨N - i, by omega, by omega⟩
  have hsub : i + j - i = j := by omega
  rw [hsub]
  -- goal: i + j − 1 ≤ i·j, with i ≥ 1, j ≥ 1; reduces to (i−1)(j−1) ≥ 0
  obtain ⟨p, rfl⟩ : ∃ p, i = 1 + p := ⟨i - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, j = 1 + q := ⟨j - 1, by omega⟩
  have hexp : (1 + p) * (1 + q) = 1 + p + q + p * q := by
    have h1 : (1 + p) * (1 + q) = (1 + p) + (1 + p) * q := by
      rw [Nat.mul_add, Nat.mul_one]
    have h2 : (1 + p) * q = q + p * q := by rw [Nat.add_mul, Nat.one_mul]
    rw [h1, h2]; omega
  rw [hexp]; omega

/-! ## The fundamental-weight Casimir `C₂(ω_i) = q_i·(N+1)/(2N)` -/

/-- `C₂(ω_i)` for `SU(N)`: `q_i·(N+1)/(2N)`, `q_i = i(N−i)`.  At `i = 1`,
`q_1 = N−1` and `C₂(ω_1) = (N−1)(N+1)/(2N) = (N²−1)/(2N) = C₂_fund`. -/
def suN_C2_fundweight (N i : Nat) (hN : 0 < N) : Q' :=
  Q'.mkPos ((suN_qWeight N i * (N + 1) : Nat) : Int) (2 * N)
    (Nat.mul_pos (by decide) hN)

/-- **Every SU(N) fundamental weight clears the `3/4` gap floor.**
`Casimir.gapFloor ≤ C₂(ω_i)` for all `1 ≤ i ≤ N−1`.  Cross-multiplied:
`6N ≤ 4·q_i·(N+1)`; from `q_i ≥ N−1` (`suN_qWeight_ge`) and the `N² ≥ 2N`
step (as in `suN_gap_lb`), `4·q_i·(N+1) ≥ 4(N²−1) ≥ 8N−4 ≥ 6N` for `N ≥ 2`. -/
theorem suN_C2_fundweight_gap_lb (N i : Nat) (hi : 1 ≤ i) (hiN : i + 1 ≤ N) :
    Casimir.gapFloor ≤ suN_C2_fundweight N i (by omega) := by
  show (Casimir.gapFloor).num * ((suN_C2_fundweight N i (by omega)).den : Int)
     ≤ (suN_C2_fundweight N i (by omega)).num * ((Casimir.gapFloor).den : Int)
  have hgn : (Casimir.gapFloor).num = (3 : Int) := rfl
  have hgd : ((Casimir.gapFloor).den : Int) = (4 : Int) := rfl
  have hfn : (suN_C2_fundweight N i (by omega)).num
      = ((suN_qWeight N i * (N + 1) : Nat) : Int) := rfl
  have hfd : ((suN_C2_fundweight N i (by omega)).den : Int) = ((2 * N : Nat) : Int) := by
    rw [suN_C2_fundweight, Q'.mkPos_den (h := by omega)]
  rw [hgn, hgd, hfn, hfd]
  -- Goal: 3 * ↑(2*N) ≤ ↑(q_i*(N+1)) * 4
  have hcast2N : (((2 * N : Nat)) : Int) = 2 * (N : Int) := by
    rw [Int.natCast_mul]; rfl
  rw [hcast2N]
  -- ↑(q_i*(N+1)) = ↑q_i * (↑N + 1)
  have hN1 : ((N + 1 : Nat) : Int) = (N : Int) + 1 := by omega
  have hmul : ((suN_qWeight N i * (N + 1) : Nat) : Int)
      = (suN_qWeight N i : Int) * ((N : Int) + 1) := by
    rw [Int.natCast_mul, hN1]
  rw [hmul]
  -- q_i ≥ N − 1, in Int (N ≥ 2)
  have hq : (N : Int) - 1 ≤ (suN_qWeight N i : Int) := by
    have hnat : N - 1 ≤ suN_qWeight N i := suN_qWeight_ge N i hi hiN
    have hcastle : ((N - 1 : Nat) : Int) ≤ (suN_qWeight N i : Int) := by exact_mod_cast hnat
    have hcast : ((N - 1 : Nat) : Int) = (N : Int) - 1 := by omega
    omega
  have hk2 : (2 : Int) ≤ (N : Int) := by
    have : 2 ≤ N := by omega
    exact_mod_cast this
  have hNp1nn : (0 : Int) ≤ (N : Int) + 1 := by omega
  -- (N−1)(N+1) ≤ q_i·(N+1)
  have step1 : ((N : Int) - 1) * ((N : Int) + 1)
      ≤ (suN_qWeight N i : Int) * ((N : Int) + 1) :=
    Int.mul_le_mul_of_nonneg_right hq hNp1nn
  -- expand (N−1)(N+1) = N²−1 (no `ring`: distribute + omega with the N² atom)
  have e_lN : ((N : Int) - 1) * (N : Int) = (N : Int) * (N : Int) - (N : Int) := by
    rw [Int.sub_mul, Int.one_mul]
  have hexpand : ((N : Int) - 1) * ((N : Int) + 1) = (N : Int) * (N : Int) - 1 := by
    rw [Int.mul_add, Int.mul_one, e_lN]; omega
  rw [hexpand] at step1
  -- N² ≥ 2N
  have hkk : (2 : Int) * (N : Int) ≤ (N : Int) * (N : Int) :=
    Int.mul_le_mul_of_nonneg_right hk2 (by omega)
  -- atoms B := q_i·(N+1), A := N²;  step1: A−1 ≤ B, hkk: 2N ≤ A, hk2: N≥2 ⟹ 6N ≤ 4B.
  omega

end YMGap.RepTheory

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RepTheory.suN_qWeight_ge
#print axioms YMGap.RepTheory.suN_C2_fundweight_gap_lb
