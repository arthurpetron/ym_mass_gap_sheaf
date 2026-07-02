/-
The general binomial theorem over `Q'`, symbolic in both variables —
`Σ_{k=0}^n C(n,k) xᵏ y^{n−k} ≃ (x+y)ⁿ` — discharging the single analytic
residual `BinomialTheorem` that the Bernstein-variance chain
(`BernsteinVariance.lean`) reduces every moment sum to.

This CLOSES the partition-of-unity leg of the Bernstein input to all `n`:
combined with `BernsteinVariance.bernstein_partition` (which was already stated
conditionally on this residual), the Bernstein weights sum to `1` for every `n`,
generalizing the fixed-`n=2` `decide` anchor.

# What is GENUINELY PROVED here (no residual, `[propext]`/`[propext,Quot.sound]`)

  * `binomialTheorem : BinomialTheorem` — the general binomial theorem, by
    induction on `n` through Pascal's recurrence.  Structure:
      - per-term shift identities `x_shift_term` / `y_shift_term` (pure
        `Q'`-ring rearrangement; the `y`-side splits on `j < n` vs `j ≥ n`,
        the latter closing by the vanishing binomial coefficient);
      - the inductive step decomposes `(x+y)^{n+1} = x·Σ + y·Σ` and matches it
        term-by-term against the head-peeled `(n+1)`-sum via Pascal
        `C(n+1,k+1) = C(n,k) + C(n,k+1)` and a four-term additive
        rearrangement.
  * `partition_of_unity : ∀ n x, Σ_k bₙₖ(x,1−x) ≃ 1` — the unconditional
    partition of unity, obtained by feeding `binomialTheorem` into
    `BernsteinVariance.bernstein_partition`.

# Honest residual (NOT assembled here)

  * `BernsteinVariance.BernsteinVarianceStmt` — the full variance identity needs,
    beyond `binomialTheorem`, the first/second moment reindexings
    (`k_mul_binom` infrastructure) and a `neg`/`sub` per-term ring
    decomposition.  That assembly is out of scope for this module; only the
    partition (`S₀`) leg is closed here.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem below reports `[propext]` / `[propext, Quot.sound]` only.  No
`Classical.*`, no `native_decide`, no `sorryAx`.  See the `#print axioms`
block at the end.
-/

import YMGap.Continuum.BernsteinVariance
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.BinomialTheorem

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG
open YMGap.Continuum.BernsteinVariance

/-! ## Pure `Q'`-ring rearrangement helpers (no subtraction) -/

/-- `a · (c · (X · Y)) ≃ c · ((a · X) · Y)` — pull the head factor `a` into the
first position of the inner product.  The `x`-shift skeleton. -/
theorem mul_pull (a c X Y : Q') :
    (a * (c * (X * Y))).eqv (c * ((a * X) * Y)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a c (X * Y))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (a * c) (c * a) (X * Y) (Q'.mul_comm_eqv a c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c a (X * Y)) ?_
  exact Q'.mul_eqv_congr_left c (a * (X * Y)) ((a * X) * Y)
    (Q'.eqv_symm (Q'.mul_assoc_eqv a X Y))

/-- `a · (c · (X · Y)) ≃ c · (X · (a · Y))` — pull the head factor `a` into the
second position of the inner product.  The `y`-shift skeleton. -/
theorem mul_pull_y (a c X Y : Q') :
    (a * (c * (X * Y))).eqv (c * (X * (a * Y))) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a c (X * Y))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (a * c) (c * a) (X * Y) (Q'.mul_comm_eqv a c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c a (X * Y)) ?_
  refine Q'.mul_eqv_congr_left c (a * (X * Y)) (X * (a * Y)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a X Y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (a * X) (X * a) Y (Q'.mul_comm_eqv a X)) ?_
  exact Q'.mul_assoc_eqv X a Y

/-- The four-term additive rearrangement the inductive step reassembles through:
`(Q + (A + B)) + P ≃ (A + P) + (Q + B)`. -/
theorem four_rearrange (A B P Q : Q') :
    ((Q + (A + B)) + P).eqv ((A + P) + (Q + B)) := by
  have hL : ((Q + (A + B)) + P).eqv ((A + B) + (P + Q)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ P (Q'.add_comm_eqv Q (A + B))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (A + B) Q P) ?_
    exact Q'.add_eqv_congr_left (A + B) _ _ (Q'.add_comm_eqv Q P)
  have hR : ((A + P) + (Q + B)).eqv ((A + B) + (P + Q)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (A + P) _ _ (Q'.add_comm_eqv Q B)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (A + P) B Q)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ Q (Q'.add_assoc_eqv A P B)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ Q
        (Q'.add_eqv_congr_left A _ _ (Q'.add_comm_eqv P B))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ Q (Q'.eqv_symm (Q'.add_assoc_eqv A B P))) ?_
    exact Q'.add_assoc_eqv (A + B) P Q
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-! ## The two shifted-monomial families -/

/-- `x`-shifted Bernstein monomial: `C(n,k)·x^{k+1}·y^{n−k}`. -/
def Tx (n : Nat) (x y : Q') (k : Nat) : Q' :=
  Q'.ofNat (binom n k) * (x ^ (k + 1) * y ^ (n - k))

/-- `y`-shifted Bernstein monomial: `C(n,k+1)·x^{k+1}·y^{n−k}`. -/
def Ty (n : Nat) (x y : Q') (k : Nat) : Q' :=
  Q'.ofNat (binom n (k + 1)) * (x ^ (k + 1) * y ^ (n - k))

/-- **`x`-shift.** `x · bₙₖ ≃ C(n,k)·x^{k+1}·y^{n−k}`, for every `k`.  Pure ring
rearrangement (`x^{k+1} = x·xᵏ` is definitional). -/
theorem x_shift_term (n : Nat) (x y : Q') (k : Nat) :
    (x * S0seq n x y k).eqv (Tx n x y k) :=
  mul_pull x (Q'.ofNat (binom n k)) (x ^ k) (y ^ (n - k))

/-- **`y`-shift.** `y · bₙ,ₖ₊₁ ≃ C(n,k+1)·x^{k+1}·y^{n−k}`, for every `k`.

Case split on `k < n` (the exponent identity `(n−(k+1))+1 = n−k`, so
`y·y^{n−(k+1)} = y^{n−k}`) vs `k ≥ n` (then `C(n,k+1) = 0`, both sides `≃ 0`). -/
theorem y_shift_term (n : Nat) (x y : Q') (j : Nat) :
    (y * S0seq n x y (j + 1)).eqv (Ty n x y j) := by
  rcases Nat.lt_or_ge j n with hjn | hjn
  · -- j < n : the exponent absorbs the head factor `y`.
    show (y * (Q'.ofNat (binom n (j + 1)) * (x ^ (j + 1) * y ^ (n - (j + 1))))).eqv
        (Q'.ofNat (binom n (j + 1)) * (x ^ (j + 1) * y ^ (n - j)))
    have hexp : n - j = (n - (j + 1)) + 1 := by omega
    rw [hexp]
    exact mul_pull_y y (Q'.ofNat (binom n (j + 1))) (x ^ (j + 1)) (y ^ (n - (j + 1)))
  · -- j ≥ n : the coefficient vanishes, both sides ≃ 0.
    have hzero : binom n (j + 1) = 0 := binom_eq_zero_of_lt n (j + 1) (by omega)
    show (y * (Q'.ofNat (binom n (j + 1)) * (x ^ (j + 1) * y ^ (n - (j + 1))))).eqv
        (Q'.ofNat (binom n (j + 1)) * (x ^ (j + 1) * y ^ (n - j)))
    rw [hzero]
    have hL : (y * (Q'.ofNat 0 * (x ^ (j + 1) * y ^ (n - (j + 1))))).eqv 0 := by
      have e1 : (Q'.ofNat 0 * (x ^ (j + 1) * y ^ (n - (j + 1)))).eqv 0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 _ Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv _)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left y _ 0 e1) ?_
      exact Q'.mul_zero_eqv y
    have hR : (Q'.ofNat 0 * (x ^ (j + 1) * y ^ (n - j))).eqv 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 _ Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv _)
    exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-! ## Small collapses reused across the induction -/

/-- `C(m,m)·(x^{m}·y^{0}) ≃ x^{m}` — the `x`-only top term. -/
theorem diag_collapse (x y : Q') (m e : Nat) :
    (Q'.ofNat (binom m m) * (x ^ e * y ^ (m - m))).eqv (x ^ e) := by
  rw [binom_self m, Nat.sub_self m]
  show (Q'.ofNat 1 * (x ^ e * (1 : Q'))).eqv (x ^ e)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 1) _ (x ^ e) (Q'.mul_one_eqv (x ^ e))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 (x ^ e) (by decide)) ?_
  exact Q'.one_mul_eqv (x ^ e)

/-- `C(m,0)·(x^{0}·y^{e}) ≃ y^{e}` — the `y`-only head term. -/
theorem head_collapse (x y : Q') (m e : Nat) :
    (Q'.ofNat (binom m 0) * (x ^ 0 * y ^ e)).eqv (y ^ e) := by
  rw [binom_zero_right m]
  show (Q'.ofNat 1 * ((1 : Q') * y ^ e)).eqv (y ^ e)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 1) _ (y ^ e) (Q'.one_mul_eqv (y ^ e))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 (y ^ e) (by decide)) ?_
  exact Q'.one_mul_eqv (y ^ e)

/-! ## The binomial theorem -/

/-- **General binomial theorem** over `Q'`, symbolic in both variables.
Discharges the `BinomialTheorem` residual of `BernsteinVariance.lean`. -/
theorem binomialTheorem : BinomialTheorem := by
  intro n
  induction n with
  | zero =>
    intro x y
    show ((0 : Q') + Q'.ofNat (binom 0 0) * (x ^ 0 * y ^ (0 - 0))).eqv ((x + y) ^ 0)
    show ((0 : Q') + Q'.ofNat 1 * ((1 : Q') * (1 : Q'))).eqv (1 : Q')
    decide
  | succ n ih =>
    intro x y
    have ihxy := ih x y
    -- x-leg : x·Σ ≃ finSum Tx (n+1)
    have x_leg : (x * finSum (S0seq n x y) (n + 1)).eqv (finSum (Tx n x y) (n + 1)) :=
      Q'.eqv_trans _ _ _ (const_mul_finSum (S0seq n x y) x (n + 1))
        (finSum_eqv_congr (fun i => x * S0seq n x y i) (Tx n x y)
          (fun i => x_shift_term n x y i) (n + 1))
    -- y-leg : y·Σ ≃ y^{n+1} + finSum Ty n
    have y_leg : (y * finSum (S0seq n x y) (n + 1)).eqv
        (y ^ (n + 1) + finSum (Ty n x y) n) := by
      refine Q'.eqv_trans _ _ _ (const_mul_finSum (S0seq n x y) y (n + 1)) ?_
      refine Q'.eqv_trans _ _ _
        (finSum_head_peel (fun i => y * S0seq n x y i) n) ?_
      have hhead : (y * S0seq n x y 0).eqv (y ^ (n + 1)) := by
        show (y * (Q'.ofNat (binom n 0) * (x ^ 0 * y ^ (n - 0)))).eqv (y ^ (n + 1))
        show (y * (Q'.ofNat (binom n 0) * (x ^ 0 * y ^ n))).eqv (y * y ^ n)
        exact Q'.mul_eqv_congr_left y _ (y ^ n) (head_collapse x y n n)
      have htail : (finSum (fun j => y * S0seq n x y (j + 1)) n).eqv
          (finSum (Ty n x y) n) :=
        finSum_eqv_congr (fun j => y * S0seq n x y (j + 1)) (Ty n x y)
          (fun j => y_shift_term n x y j) n
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (finSum (fun j => y * S0seq n x y (j + 1)) n) hhead)
        (Q'.add_eqv_congr_left (y ^ (n + 1)) _ _ htail)
    -- RHS : (x+y)^{n+1} ≃ (finSum Tx n + x^{n+1}) + (y^{n+1} + finSum Ty n)
    have hRHS : ((x + y) ^ (n + 1)).eqv
        ((finSum (Tx n x y) n + x ^ (n + 1)) + (y ^ (n + 1) + finSum (Ty n x y) n)) := by
      show ((x + y) * (x + y) ^ n).eqv _
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (x + y) ((x + y) ^ n)
          (finSum (S0seq n x y) (n + 1)) (Q'.eqv_symm ihxy)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv x y (finSum (S0seq n x y) (n + 1))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (y * finSum (S0seq n x y) (n + 1)) x_leg) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (finSum (Tx n x y) (n + 1)) _ _ y_leg) ?_
      refine Q'.add_eqv_congr_right _ _ (y ^ (n + 1) + finSum (Ty n x y) n) ?_
      -- finSum Tx (n+1) = finSum Tx n + Tx n ≃ finSum Tx n + x^{n+1}
      show (finSum (Tx n x y) n + Tx n x y n).eqv (finSum (Tx n x y) n + x ^ (n + 1))
      exact Q'.add_eqv_congr_left (finSum (Tx n x y) n) _ _
        (diag_collapse x y n (n + 1))
    -- LHS : finSum (S0seq (n+1)) (n+2) ≃ (y^{n+1} + (finSum Tx n + finSum Ty n)) + x^{n+1}
    have htop : (S0seq (n + 1) x y (n + 1)).eqv (x ^ (n + 1)) := by
      show (Q'.ofNat (binom (n + 1) (n + 1)) *
            (x ^ (n + 1) * y ^ ((n + 1) - (n + 1)))).eqv (x ^ (n + 1))
      exact diag_collapse x y (n + 1) (n + 1)
    have hmid : ∀ j, (S0seq (n + 1) x y (j + 1)).eqv (Tx n x y j + Ty n x y j) := by
      intro j
      show (Q'.ofNat (binom (n + 1) (j + 1)) *
            (x ^ (j + 1) * y ^ ((n + 1) - (j + 1)))).eqv (Tx n x y j + Ty n x y j)
      have hs : (n + 1) - (j + 1) = n - j := by omega
      rw [hs, binom_succ_succ n j]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (x ^ (j + 1) * y ^ (n - j))
          (Q'.ofNat_add_eqv (binom n j) (binom n (j + 1)))) ?_
      exact Q'.add_mul_eqv (Q'.ofNat (binom n j)) (Q'.ofNat (binom n (j + 1)))
        (x ^ (j + 1) * y ^ (n - j))
    have hfirst : (finSum (S0seq (n + 1) x y) (n + 1)).eqv
        (y ^ (n + 1) + (finSum (Tx n x y) n + finSum (Ty n x y) n)) := by
      refine Q'.eqv_trans _ _ _ (finSum_head_peel (S0seq (n + 1) x y) n) ?_
      have hhead0 : (S0seq (n + 1) x y 0).eqv (y ^ (n + 1)) := by
        show (Q'.ofNat (binom (n + 1) 0) * (x ^ 0 * y ^ ((n + 1) - 0))).eqv (y ^ (n + 1))
        exact head_collapse x y (n + 1) (n + 1)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (finSum (fun j => S0seq (n + 1) x y (j + 1)) n) hhead0) ?_
      refine Q'.add_eqv_congr_left (y ^ (n + 1)) _ _ ?_
      refine Q'.eqv_trans _ _ _
        (finSum_eqv_congr (fun j => S0seq (n + 1) x y (j + 1))
          (fun j => Tx n x y j + Ty n x y j) hmid n) ?_
      exact finSum_add (Tx n x y) (Ty n x y) n
    have hLHS : (finSum (S0seq (n + 1) x y) (n + 2)).eqv
        ((y ^ (n + 1) + (finSum (Tx n x y) n + finSum (Ty n x y) n)) + x ^ (n + 1)) := by
      show (finSum (S0seq (n + 1) x y) (n + 1) + S0seq (n + 1) x y (n + 1)).eqv _
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (S0seq (n + 1) x y (n + 1)) hfirst)
        (Q'.add_eqv_congr_left _ _ (x ^ (n + 1)) htop)
    -- Combine.
    exact Q'.eqv_trans _ _ _ hLHS
      (Q'.eqv_trans _ _ _
        (four_rearrange (finSum (Tx n x y) n) (finSum (Ty n x y) n)
          (x ^ (n + 1)) (y ^ (n + 1)))
        (Q'.eqv_symm hRHS))

/-! ## Downstream: unconditional partition of unity -/

/-- **Partition of unity**, now UNCONDITIONAL for every `n`:
`Σ_{k=0}^n C(n,k) xᵏ (1−x)^{n−k} ≃ 1`.  Feeds `binomialTheorem` into the
previously-conditional `BernsteinVariance.bernstein_partition`. -/
theorem partition_of_unity (n : Nat) (x : Q') :
    (finSum (fun k => bmono n x (1 - x) k) (n + 1)).eqv 1 :=
  bernstein_partition binomialTheorem n x

end YMGap.Continuum.BinomialTheorem

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BinomialTheorem.mul_pull
#print axioms YMGap.Continuum.BinomialTheorem.mul_pull_y
#print axioms YMGap.Continuum.BinomialTheorem.four_rearrange
#print axioms YMGap.Continuum.BinomialTheorem.x_shift_term
#print axioms YMGap.Continuum.BinomialTheorem.y_shift_term
#print axioms YMGap.Continuum.BinomialTheorem.diag_collapse
#print axioms YMGap.Continuum.BinomialTheorem.head_collapse
#print axioms YMGap.Continuum.BinomialTheorem.binomialTheorem
#print axioms YMGap.Continuum.BinomialTheorem.partition_of_unity
