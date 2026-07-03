/-
Discharging the leg-(A) crux `CubicEulerBound` of the tree-graph reduction.

# The object being proved

`YMGap.Continuum.TreeGraphBoundProgress.CubicEulerBound` is the single NAMED
leg-(A) arithmetic input of the Kotecký–Preiss tree-graph reduction:

    CubicEulerBound : Prop := ∀ n : Nat, (n + 1) ^ n ≤ 3 * n ^ n

i.e. the standard `(1 + 1/n)^n ≤ 3` bound (`e < 3`).  Everything downstream of
it (`powSelf_le`, `eulerArithNat`, `legA`, `tree_graph_of_reduction`,
`TreeGraphReduction.toBound`) is already PROVED in `TreeGraphBoundProgress`
taking this as a hypothesis.  This module DISCHARGES it unconditionally:

    theorem cubicEulerBound : CubicEulerBound

so leg (A) is closed and the master reduction now depends only on the two
genuinely-open combinatorial legs (P) Penrose sign domination and (C) Cayley.

# The proof (entirely in `Nat`, Mathlib-free)

Naive strong induction on `(n+1)^n ≤ 3·n^n` FAILS (the ratio `(1+1/n)^n` is
INCREASING, so the bound does not propagate).  Instead we use the standard
decreasing-sequence argument, packaged as an integer-arithmetic monotonicity:

1. `natBernoulli`  — `A^(m+1) + (m+1)·A^m ≤ (A+1)^(m+1)`   (induction on `m`).
2. `monoStep`      — `(n+2)^(n+2)·n^(n+1) ≤ (n+1)^(2n+3)`   (Bernoulli at
   `A = (n+2)·n`, `A+1 = (n+1)²`, then one `le_add` slack of `A^n`).
3. `dBoundK`       — `(n+1)^(n+1) ≤ 3·n^(n+1)` for `n ≥ 5`   (induction, base
   `n=5`: `6^6 = 46656 ≤ 46875 = 3·5^6`; step via `monoStep` + cancel `n^(n+1)`).
4. `cubicEulerBound` — assemble: `n < 5` by `decide`; `n ≥ 5` from `dBoundK`
   by cancelling `(n+1)`.

All Nat polynomial identities are discharged by distribute-then-AC-normalise
`simp only [Nat.mul_add, …, Nat.mul_assoc, …]` (no `ring`, which is Mathlib).

# Axiom-gate (AGENTS.md Rule 1)

`cubicEulerBound` reports `[propext]` (and `Quot.sound`) only.  No `sorryAx`,
no `Classical.*`, no `native_decide`, no custom axiom.
-/

import YMGap.Continuum.TreeGraphBoundProgress

namespace YMGap.Continuum.CubicEulerBoundProof

open YMGap.Continuum.TreeGraphBoundProgress (CubicEulerBound)

/-! ## 1. Nat Bernoulli -/

/-- **Nat Bernoulli.**  `A^(m+1) + (m+1)·A^m ≤ (A+1)^(m+1)` — the first two
terms of the binomial expansion of `(A+1)^(m+1)`.  Proved by induction on `m`. -/
theorem natBernoulli : ∀ (A m : Nat), A ^ (m + 1) + (m + 1) * A ^ m ≤ (A + 1) ^ (m + 1)
  | A, 0 => by
      show A ^ (0 + 1) + (0 + 1) * A ^ 0 ≤ (A + 1) ^ (0 + 1)
      simp
  | A, m + 1 => by
      have ih := natBernoulli A m
      have hpm1 : A ^ (m + 1) = A ^ m * A := Nat.pow_succ A m
      have hpm2 : A ^ (m + 1 + 1) = A ^ m * A * A := by
        rw [Nat.pow_succ, Nat.pow_succ]
      have key : (A + 1) * (A ^ (m + 1) + (m + 1) * A ^ m)
          = A ^ (m + 1 + 1) + (m + 1 + 1) * A ^ (m + 1) + (m + 1) * A ^ m := by
        rw [hpm1, hpm2]
        simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.mul_succ, Nat.one_mul,
          Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
      have hstep : (A + 1) * (A ^ (m + 1) + (m + 1) * A ^ m) ≤ (A + 1) * (A + 1) ^ (m + 1) :=
        Nat.mul_le_mul (Nat.le_refl _) ih
      have hpow : (A + 1) * (A + 1) ^ (m + 1) = (A + 1) ^ (m + 1 + 1) := by
        rw [Nat.mul_comm (A + 1) ((A + 1) ^ (m + 1))]
        exact (Nat.pow_succ (A + 1) (m + 1)).symm
      calc A ^ (m + 1 + 1) + (m + 1 + 1) * A ^ (m + 1)
          ≤ A ^ (m + 1 + 1) + (m + 1 + 1) * A ^ (m + 1) + (m + 1) * A ^ m :=
            Nat.le_add_right _ _
        _ = (A + 1) * (A ^ (m + 1) + (m + 1) * A ^ m) := key.symm
        _ ≤ (A + 1) * (A + 1) ^ (m + 1) := hstep
        _ = (A + 1) ^ (m + 1 + 1) := hpow

/-! ## 2. Monotone step -/

/-- **Monotone step.**  `(n+2)^(n+2)·n^(n+1) ≤ (n+1)^(2n+3)` — the discrete
monotonicity `((n+1)/n)^(n+1) ↓`.  Proof: Bernoulli at `A = (n+2)·n`
(`A+1 = (n+1)²`), scaled by `(n+1)`, with the reshaped LHS `A^(n+1)·(n+2)`
absorbing an `A^n` slack via `le_add`. -/
theorem monoStep (n : Nat) :
    (n + 2) ^ (n + 2) * n ^ (n + 1) ≤ (n + 1) ^ (2 * n + 3) := by
  -- Bernoulli at A = (n+2)*n, m = n
  have hB := natBernoulli ((n + 2) * n) n
  -- (n+2)*n + 1 = (n+1)*(n+1)
  have hAA1 : (n + 2) * n + 1 = (n + 1) * (n + 1) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.mul_succ, Nat.one_mul,
      Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
  -- reshape Bernoulli RHS
  have hBR : ((n + 2) * n + 1) ^ (n + 1) = (n + 1) ^ (n + 1) * (n + 1) ^ (n + 1) := by
    rw [hAA1, Nat.mul_pow]
  -- scale Bernoulli by (n+1)
  have hBmul : (n + 1) * (((n + 2) * n) ^ (n + 1) + (n + 1) * ((n + 2) * n) ^ n)
      ≤ (n + 1) * ((n + 1) ^ (n + 1) * (n + 1) ^ (n + 1)) := by
    rw [← hBR]; exact Nat.mul_le_mul (Nat.le_refl _) hB
  -- the scaled RHS is (n+1)^(2n+3)
  have hRHSpow : (n + 1) * ((n + 1) ^ (n + 1) * (n + 1) ^ (n + 1)) = (n + 1) ^ (2 * n + 3) := by
    have h1 : (n + 1) ^ (n + 1) * (n + 1) ^ (n + 1) = (n + 1) ^ ((n + 1) + (n + 1)) :=
      (Nat.pow_add (n + 1) (n + 1) (n + 1)).symm
    rw [h1, Nat.mul_comm (n + 1) ((n + 1) ^ ((n + 1) + (n + 1))), ← Nat.pow_succ]
    congr 1
    omega
  -- reshape the target LHS to A^(n+1)*(n+2)
  have hLHSr : (n + 2) ^ (n + 2) * n ^ (n + 1) = ((n + 2) * n) ^ (n + 1) * (n + 2) := by
    have e : (n + 2) ^ (n + 2) = (n + 2) ^ (n + 1) * (n + 2) := Nat.pow_succ (n + 2) (n + 1)
    rw [e, Nat.mul_pow]
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  -- the algebraic identity closing leg-(A) monotonicity
  have hAsucc : ((n + 2) * n) ^ (n + 1) = ((n + 2) * n) ^ n * ((n + 2) * n) :=
    Nat.pow_succ ((n + 2) * n) n
  have eqM : (n + 1) * (((n + 2) * n) ^ (n + 1) + (n + 1) * ((n + 2) * n) ^ n)
      = ((n + 2) * n) ^ (n + 1) * (n + 2) + ((n + 2) * n) ^ n := by
    rw [hAsucc]
    simp only [Nat.mul_add, Nat.add_mul, Nat.succ_mul, Nat.mul_succ, Nat.one_mul,
      Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc]
  -- assemble
  have hLHSalg : (n + 2) ^ (n + 2) * n ^ (n + 1)
      ≤ (n + 1) * (((n + 2) * n) ^ (n + 1) + (n + 1) * ((n + 2) * n) ^ n) := by
    rw [hLHSr, eqM]
    exact Nat.le_add_right _ _
  calc (n + 2) ^ (n + 2) * n ^ (n + 1)
      ≤ (n + 1) * (((n + 2) * n) ^ (n + 1) + (n + 1) * ((n + 2) * n) ^ n) := hLHSalg
    _ ≤ (n + 1) * ((n + 1) ^ (n + 1) * (n + 1) ^ (n + 1)) := hBmul
    _ = (n + 1) ^ (2 * n + 3) := hRHSpow

/-! ## 3. The `n ≥ 5` bound `(n+1)^(n+1) ≤ 3·n^(n+1)` -/

/-- One inductive step of the `D(n)` bound: from `(n+1)^(n+1) ≤ 3·n^(n+1)`
derive `(n+2)^(n+2) ≤ 3·(n+1)^(n+2)`, using `monoStep` and cancelling the
positive `n^(n+1)`. -/
theorem dStep (n : Nat) (hn : 0 < n)
    (ih : (n + 1) ^ (n + 1) ≤ 3 * n ^ (n + 1)) :
    (n + 2) ^ (n + 2) ≤ 3 * (n + 1) ^ (n + 2) := by
  have hmono := monoStep n
  have hsplit : (n + 1) ^ (2 * n + 3) = (n + 1) ^ (n + 1) * (n + 1) ^ (n + 2) := by
    rw [show 2 * n + 3 = (n + 1) + (n + 2) from by omega, Nat.pow_add]
  have hih : (n + 1) ^ (n + 1) * (n + 1) ^ (n + 2) ≤ (3 * n ^ (n + 1)) * (n + 1) ^ (n + 2) :=
    Nat.mul_le_mul ih (Nat.le_refl _)
  rw [hsplit] at hmono
  have hchain : (n + 2) ^ (n + 2) * n ^ (n + 1) ≤ (3 * n ^ (n + 1)) * (n + 1) ^ (n + 2) :=
    Nat.le_trans hmono hih
  have hrear : (3 * n ^ (n + 1)) * (n + 1) ^ (n + 2) = (3 * (n + 1) ^ (n + 2)) * n ^ (n + 1) := by
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hrear] at hchain
  exact Nat.le_of_mul_le_mul_right hchain (Nat.pow_pos hn)

/-- `D(n)` for `n = k + 5`: `(n+1)^(n+1) ≤ 3·n^(n+1)`, by induction on `k`. -/
theorem dBoundK : ∀ k : Nat, (k + 5 + 1) ^ (k + 5 + 1) ≤ 3 * (k + 5) ^ (k + 5 + 1)
  | 0 => by decide
  | k + 1 => by
      have ih := dBoundK k
      exact dStep (k + 5) (by omega) ih

/-! ## 4. Assembly -/

/-- From `D(m)` (`m ≥ 1`), derive `(m+1)^m ≤ 3·m^m` by cancelling `(m+1)`. -/
theorem cubicStep (m : Nat) (hm : 0 < m)
    (hD : (m + 1) ^ (m + 1) ≤ 3 * m ^ (m + 1)) :
    (m + 1) ^ m ≤ 3 * m ^ m := by
  have e1 : (m + 1) ^ (m + 1) = (m + 1) ^ m * (m + 1) := Nat.pow_succ (m + 1) m
  have e2 : 3 * m ^ (m + 1) = 3 * m ^ m * m := by
    rw [Nat.pow_succ, Nat.mul_assoc]
  have step : (m + 1) ^ m * (m + 1) ≤ 3 * m ^ m * (m + 1) := by
    calc (m + 1) ^ m * (m + 1) = (m + 1) ^ (m + 1) := e1.symm
      _ ≤ 3 * m ^ (m + 1) := hD
      _ = 3 * m ^ m * m := e2
      _ ≤ 3 * m ^ m * (m + 1) := Nat.mul_le_mul (Nat.le_refl _) (Nat.le_succ m)
  exact Nat.le_of_mul_le_mul_right step (Nat.succ_pos m)

/-- **The leg-(A) crux, DISCHARGED.**  `(n+1)^n ≤ 3·n^n` for all `n`, i.e. the
standard `e < 3` bound.  `n < 5` by `decide`; `n ≥ 5` from `dBoundK`. -/
theorem cubicEulerBound : CubicEulerBound := by
  intro n
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | k + 5 => exact cubicStep (k + 5) (by omega) (dBoundK k)

end YMGap.Continuum.CubicEulerBoundProof

/-! ## Axiom-dependency gate (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CubicEulerBoundProof.natBernoulli
#print axioms YMGap.Continuum.CubicEulerBoundProof.monoStep
#print axioms YMGap.Continuum.CubicEulerBoundProof.dBoundK
#print axioms YMGap.Continuum.CubicEulerBoundProof.cubicEulerBound
