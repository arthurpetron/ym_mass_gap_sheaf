/-
Bernstein moments — the division-free variance identity `Σ (k − n x)²·bₙₖ =
n·x(1−x)`, built from the general binomial theorem.

This module delivers the genuinely-closeable, self-contained pieces of the
Bernstein-variance lemma chain and reduces the remaining analytic content to
ONE honestly named residual (the binomial theorem `BinomialTheorem`).  No
`sorry`, no custom axiom.

# What is GENUINELY PROVED here (no residual, `[propext]`-only)

  * `binom_one`  — `C(n,1) = n` (Pascal induction).
  * `k_mul_binom` — the combinatorial absorption identity
      `(n+1)·C(n,k) = C(n+1,k+1)·(k+1)`  (double recursion on `n,k`).
    This is the subtraction-free form of `k·C(n,k) = n·C(n−1,k−1)`; commuting
    the product gives the reindexing form `(k+1)·C(n+1,k+1) = (n+1)·C(n,k)`
    (`succ_mul_binom_reindex`) that a head-peeled first moment consumes.  It is
    the only combinatorial input the moment reindexing needs.
  * `finSum_head_peel` / `finSum_head_peel_zero` — head-peel of a `finSum`
    (`Σ_{k<n+1} f k ≃ f 0 + Σ_{j<n} f(j+1)`), and the corollary that a
    zero-headed sum drops its head.  (`finSum` has no `range_succ'`; this adds
    it.)
  * `eqv_one_pow` — `q ≃ 1 → qⁿ ≃ 1`.
  * `add_one_sub_eqv_one` — `x + (1 − x) ≃ 1`.
  * `bernstein_partition` — **partition of unity** `Σ_k bₙₖ(x,1−x) ≃ 1` for
    every `n`, derived from the binomial-theorem residual.  Generalizes the
    fixed-`n=2` `bernstein_partition_scaled_n2` anchor.

# What is reduced to an HONEST NAMED RESIDUAL (a `Prop` statement, no proof)

  * `BinomialTheorem` — `Σ_{k=0}^n C(n,k) xᵏ y^{n−k} ≃ (x+y)ⁿ`, kept symbolic
    in `y`.  The single genuine analytic wall; every downstream moment
    (`S₀`, `S₁`, `S₂`) reduces to it via `k_mul_binom` + `finSum_head_peel`.
  * `BernsteinVarianceStmt` — the scaled variance identity itself, whose
    reduction to `BinomialTheorem` (through the per-term ring decomposition
    `(a − t)² = a(a−1) + (1−2t)a + t²` and the scalar collapse
    `n(n−1)x² + (1−2nx)nx + (nx)² = n·x(1−x)`) is documented but not assembled
    here (it needs a `neg`/`sub` distribution kit beyond this module's scope).

# Axiom-gate (AGENTS.md Rule 1)

Every theorem below reports `[propext]` / `[propext, Quot.sound]` only.  No
`Classical.*`, no `native_decide`, no `sorryAx`.  See the `#print axioms`
block at the end.
-/

import YMGap.RG.PolylogTail
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.BernsteinVariance

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG

/-! ## Combinatorial input (`Nat`) -/

/-- `C(n,1) = n`, by Pascal induction. -/
theorem binom_one : ∀ n, binom n 1 = n
  | 0 => rfl
  | n + 1 => by
      have hp : binom (n + 1) 1 = binom n 0 + binom n 1 := binom_succ_succ n 0
      rw [hp, binom_zero_right, binom_one n]
      omega

/-- **Absorption identity** `(n+1)·C(n,k) = C(n+1,k+1)·(k+1)`.

The subtraction-free form of `k·C(n,k) = n·C(n−1,k−1)`.  Double recursion on
`n` and `k`, exactly the Pascal double-recursion `succ_mul_choose_eq`. -/
theorem k_mul_binom : ∀ n k, (n + 1) * binom n k = binom (n + 1) (k + 1) * (k + 1)
  | 0, 0 => rfl
  | 0, k + 1 => by
      have hl : binom 0 (k + 1) = 0 := rfl
      have hr : binom 1 (k + 2) = 0 := rfl
      rw [hl, hr]
      omega
  | n + 1, 0 => by
      have hl : binom (n + 1) 0 = 1 := binom_zero_right (n + 1)
      have hr : binom (n + 2) 1 = n + 2 := binom_one (n + 2)
      rw [hl, hr]
  | n + 1, k + 1 => by
      have pas : binom (n + 2) (k + 2)
          = binom (n + 1) (k + 1) + binom (n + 1) (k + 2) := binom_succ_succ (n + 1) (k + 1)
      have pasL : binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := binom_succ_succ n k
      have ih1 : (n + 1) * binom n k = binom (n + 1) (k + 1) * (k + 1) := k_mul_binom n k
      have ih2 : (n + 1) * binom n (k + 1) = binom (n + 1) (k + 2) * (k + 2) :=
        k_mul_binom n (k + 1)
      -- goal : (n+2)·C(n+1,k+1) = C(n+2,k+2)·(k+2)
      -- distribute the RHS with EXPLICIT args so `add_mul` cannot hit the LHS `(n+2)·C1`
      rw [pas, Nat.add_mul (binom (n + 1) (k + 1)) (binom (n + 1) (k + 2)) (k + 1 + 1)]
      -- RHS : C1·(k+2) + C2·(k+2)
      rw [← ih2]                        -- C2·(k+2) → (n+1)·B
      rw [Nat.mul_succ]                 -- C1·(k+2) → C1·(k+1) + C1
      rw [← ih1]                        -- C1·(k+1) → (n+1)·A
      rw [pasL]                         -- every remaining C1 → A + B (LHS and RHS)
      -- goal : (n+2)·(A+B) = ((n+1)·A + (A+B)) + (n+1)·B
      rw [Nat.succ_mul (n + 1) (binom n k + binom n (k + 1)),
          Nat.mul_add (n + 1) (binom n k) (binom n (k + 1))]
      generalize (n + 1) * binom n k = P
      generalize (n + 1) * binom n (k + 1) = Q
      omega

/-- Reindexing form: `(k+1)·C(n+1,k+1) = (n+1)·C(n,k)`, i.e. `k_mul_binom` with
the product commuted — the shape a head-peeled first moment consumes. -/
theorem succ_mul_binom_reindex (n k : Nat) :
    (k + 1) * binom (n + 1) (k + 1) = (n + 1) * binom n k := by
  rw [Nat.mul_comm (k + 1) (binom (n + 1) (k + 1))]
  exact (k_mul_binom n k).symm

/-! ## Head-peel for `finSum` (`range_succ'`) -/

/-- **Head-peel.** `Σ_{k<n+1} f k ≃ f 0 + Σ_{j<n} f (j+1)`. -/
theorem finSum_head_peel (f : QSeq) :
    ∀ n, (finSum f (n + 1)).eqv (f 0 + finSum (fun j => f (j + 1)) n)
  | 0 => by
      show ((0 : Q') + f 0).eqv (f 0 + (0 : Q'))
      rw [Q'.zero_add', Q'.add_zero']
      exact Q'.eqv_refl (f 0)
  | n + 1 => by
      show (finSum f (n + 1) + f (n + 1)).eqv
          (f 0 + finSum (fun j => f (j + 1)) (n + 1))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f (n + 1)) (finSum_head_peel f n)) ?_
      exact Q'.add_assoc_eqv (f 0) (finSum (fun j => f (j + 1)) n) (f (n + 1))

/-- Zero-headed sums drop their head:
`f 0 ≃ 0 → Σ_{k<n+1} f k ≃ Σ_{j<n} f (j+1)`. -/
theorem finSum_head_peel_zero (f : QSeq) (n : Nat) (h : (f 0).eqv 0) :
    (finSum f (n + 1)).eqv (finSum (fun j => f (j + 1)) n) := by
  refine Q'.eqv_trans _ _ _ (finSum_head_peel f n) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (finSum (fun j => f (j + 1)) n) h) ?_
  rw [Q'.zero_add']
  exact Q'.eqv_refl _

/-! ## Small `Q'` facts for the partition-of-unity collapse -/

/-- `a + (−a) ≃ 0`. -/
theorem add_neg_self_eqv (a : Q') : (a + (-a)).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_comm_eqv a (-a)) (Q'.neg_add_self_eqv a)

/-- `x + (1 − x) ≃ 1`. -/
theorem add_one_sub_eqv_one (x : Q') : (x + (1 - x)).eqv 1 := by
  have e1 : (x + (1 - x)).eqv (x + ((-x) + 1)) :=
    Q'.add_eqv_congr_left x (1 - x) ((-x) + 1) (Q'.add_comm_eqv 1 (-x))
  have e2 : (x + ((-x) + 1)).eqv ((x + (-x)) + 1) :=
    Q'.eqv_symm (Q'.add_assoc_eqv x (-x) 1)
  have e3 : ((x + (-x)) + 1).eqv ((0 : Q') + 1) :=
    Q'.add_eqv_congr_right _ _ 1 (add_neg_self_eqv x)
  have e4 : ((0 : Q') + 1).eqv 1 := by
    rw [Q'.zero_add']
    exact Q'.eqv_refl 1
  exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3 e4))

/-- `q ≃ 1 → qⁿ ≃ 1`. -/
theorem eqv_one_pow (q : Q') (h : q.eqv 1) : ∀ (n : Nat), (q ^ n).eqv 1
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      show (q * q ^ n).eqv 1
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right q 1 (q ^ n) h) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 1 (q ^ n) 1 (eqv_one_pow q h n)) ?_
      exact Q'.one_mul_eqv 1

/-! ## Bernstein monomials and moment sequences -/

/-- Bernstein monomial weight `C(n,k)·xᵏ·y^{n−k}` (`y` kept FREE). -/
def bmono (n : Nat) (x y : Q') (k : Nat) : Q' :=
  Q'.ofNat (binom n k) * (x ^ k * y ^ (n - k))

/-- Zeroth-moment sequence: the bare Bernstein weight. -/
def S0seq (n : Nat) (x y : Q') (k : Nat) : Q' := bmono n x y k

/-- First-moment sequence: `k · bₙₖ`. -/
def S1seq (n : Nat) (x y : Q') (k : Nat) : Q' := Q'.ofNat k * bmono n x y k

/-- Second (falling-factorial) moment sequence: `k(k−1) · bₙₖ`. -/
def S2seq (n : Nat) (x y : Q') (k : Nat) : Q' := Q'.ofNat (k * (k - 1)) * bmono n x y k

/-! ## The single analytic residual: the binomial theorem -/

/-- **Binomial-theorem residual.**  `Σ_{k=0}^n C(n,k) xᵏ y^{n−k} ≃ (x+y)ⁿ`, kept
symbolic in `y`.  This is the one genuine analytic wall of the Bernstein chain;
its `n=2` instance is the `bernstein_partition_scaled_n2` `decide` anchor. -/
def BinomialTheorem : Prop :=
  ∀ (n : Nat) (x y : Q'), (finSum (S0seq n x y) (n + 1)).eqv ((x + y) ^ n)

/-- **Bernstein-variance residual** (the final scaled target).  Reduces to
`BinomialTheorem` through `k_mul_binom` + the two fixed-arity ring identities;
that assembly is not carried out in this module. -/
def BernsteinVarianceStmt : Prop :=
  ∀ (n : Nat) (x : Q'),
    (finSum (fun k => (Q'.ofNat k - Q'.ofNat n * x) * (Q'.ofNat k - Q'.ofNat n * x)
                      * bmono n x (1 - x) k) (n + 1)).eqv
      (Q'.ofNat n * (x * (1 - x)))

/-! ## Partition of unity — a GENUINE reduction to the binomial-theorem residual -/

/-- **Partition of unity** for the Bernstein weights, for every `n`:
`Σ_{k=0}^n C(n,k) xᵏ (1−x)^{n−k} ≃ 1`, derived from `BinomialTheorem` via
`add_one_sub_eqv_one` + `eqv_one_pow`.  Generalizes `bernstein_partition_scaled_n2`
to all `n`. -/
theorem bernstein_partition (H : BinomialTheorem) (n : Nat) (x : Q') :
    (finSum (fun k => bmono n x (1 - x) k) (n + 1)).eqv 1 := by
  refine Q'.eqv_trans _ _ _ (H n x (1 - x)) ?_
  exact eqv_one_pow (x + (1 - x)) (add_one_sub_eqv_one x) n

end YMGap.Continuum.BernsteinVariance

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BernsteinVariance.binom_one
#print axioms YMGap.Continuum.BernsteinVariance.k_mul_binom
#print axioms YMGap.Continuum.BernsteinVariance.succ_mul_binom_reindex
#print axioms YMGap.Continuum.BernsteinVariance.finSum_head_peel
#print axioms YMGap.Continuum.BernsteinVariance.finSum_head_peel_zero
#print axioms YMGap.Continuum.BernsteinVariance.add_neg_self_eqv
#print axioms YMGap.Continuum.BernsteinVariance.add_one_sub_eqv_one
#print axioms YMGap.Continuum.BernsteinVariance.eqv_one_pow
#print axioms YMGap.Continuum.BernsteinVariance.bernstein_partition
