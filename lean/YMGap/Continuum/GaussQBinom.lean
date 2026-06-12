/-
# Gauss's q-binomial identity over `Q'` (Wall-2 finite engine — the Gaussian-weight analogue of `UTelescope`)

The continuum-positivity program's heat-kernel identity needs the
*Gaussian* weight `a^{n²}` of the Jacobi theta function `ϑ₃`.  The
geometric-weight telescoping engine (`UTelescope.uTelescope_all`,
`Σ U_n zⁿ = 1/(1−2xz+z²)`) handles a *geometric* `zⁿ`-weighted series but
cannot reach `q^{n²}`.  The missing finite combinatorial heart is **Gauss's
q-binomial identity**, which produces exactly the `q^{k²}` Gaussian
coefficients:

    ∏_{j=1}^{N} (1 + z·q^{2j−1})  ≈  Σ_{k=0}^{N} q^{k²} · ⟨N,k⟩_{q²} · z^k,

where `⟨N,k⟩_Q` is the Gaussian binomial coefficient (q-binomial) with base
`Q = q²`.  This module formalizes it over the project's constructive
rationals `Q'`, for ALL `N`, by induction on `N` driven by the q-Pascal
recurrence — the exact analogue of `UTelescope.lean`'s Chebyshev-`U`
telescoping, but for the theta weight rather than the geometric weight.

## Definition choices

`Q'` has no division (Rule 3 forbids Mathlib `ℝ`; `Q'` is the unnormalized
exact-rational substrate), so the q-binomial is defined **recursively via
q-Pascal**, never via a q-factorial quotient.  On structural recursion of
both `N` and `k` (so no `Nat` truncated subtraction enters the *definition*):

    qbin Q 0       0       = 1
    qbin Q 0       (k+1)   = 0
    qbin Q (N+1)   0       = 1
    qbin Q (N+1)   (k+1)   = qbin Q N (k+1) + Q^(N−k) · qbin Q N k

This is exactly the Gaussian-binomial recursion `⟨N+1,k⟩ = ⟨N,k⟩ +
Q^{(N+1)−k}·⟨N,k−1⟩` (here `(N+1)−(k+1) = N−k` and `(k+1)−1 = k`, both
structural).  Out-of-range entries are `0`, so the recursion is exact for all
indices.  `z, q` are carried as general `Q'` parameters (the application puts
`z = e^{iθ}`, `q = a`, but the identity is purely algebraic, exactly as
`uTelescope_all` is general in `x, z`).

## Method (mirrors `UTelescope.lean`)

No `ring`/`linarith`/`Mathlib` for `Q'` identities (AGENTS.md Rule 3):
polynomial identities hold only up to `Q'.eqv`, with the two sides generally
carrying different denominators.  Everything routes through the proven
`Q'.eqv` ring layer (`add_mul_eqv`, `mul_add_eqv`, `mul_eqv_congr`,
`add_eqv_congr`, the congruences, `add_swap_inner`, …), keeping powers as
opaque atoms via `Q'.pow_succ` (a `rfl`).

### The induction

Write `P(N) = qProd z q N = ∏_{j=1}^{N}(1 + z·q^{2j−1})` and
`G(N) = gaussSum z q N = Σ_{k=0}^{N} q^{k²}·qbin (q·q) N k·z^k`.  The product
recursion `P(N+1) = P(N)·(1 + z·q^{2N+1})` and the inductive hypothesis
`P(N) ≈ G(N)` reduce the step to the pure finite-sum identity
(`gaussSum_step`, no product left)

    G(N) · (1 + z·q^{2N+1})  ≈  G(N+1),

which is the algebraic core: multiplying the sum by `1` reproduces the first
half of every q-Pascal split, multiplying by `z·q^{2N+1}` shifts `k ↦ k+1` and
— since `q^{(k)²}·q^{2N+1} = q^{((k+1)²)}·q^{2(N−k)}` and `Q = q·q` —
reproduces the second half `Q^{(N+1)−(k+1)}·⟨N,k⟩`.  The two halves combine by
q-Pascal into `⟨N+1,·⟩`.

## Axiom gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only via the reused `Int`/`omega` helpers in the `Q'`
base layer).  No `Classical.*`, no `sorry`/`sorryAx`, no `native_decide`.
-/

import YMGap.Constructive.Geometric
import YMGap.Constructive.FinSumAlg
import YMGap.Continuum.ChebyshevBound

namespace YMGap.Continuum.GaussQBinom

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## The q-binomial (Gaussian binomial) over `Q'`

Recursive q-Pascal definition; see module docstring.  No division. -/

/-- The Gaussian binomial coefficient `⟨N,k⟩_Q` over `Q'`, defined by the
q-Pascal recurrence on structural recursion of `N` then `k`.  Out-of-range
entries (`k > N`) are `0`. -/
def qbin (Q : Q') : Nat → Nat → Q'
  | 0,     0     => 1
  | 0,     _+1   => 0
  | _+1,   0     => 1
  | N+1,   k+1   => qbin Q N (k+1) + Q ^ (N - k) * qbin Q N k

@[simp] theorem qbin_zero_zero (Q : Q') : qbin Q 0 0 = 1 := rfl
@[simp] theorem qbin_zero_succ (Q : Q') (k : Nat) : qbin Q 0 (k+1) = 0 := rfl
@[simp] theorem qbin_succ_zero (Q : Q') (N : Nat) : qbin Q (N+1) 0 = 1 := rfl

/-- **q-Pascal recurrence** (definitional, `rfl`):
`⟨N+1,k+1⟩_Q = ⟨N,k+1⟩_Q + Q^{N−k}·⟨N,k⟩_Q`. -/
@[simp] theorem qbin_succ_succ (Q : Q') (N k : Nat) :
    qbin Q (N+1) (k+1) = qbin Q N (k+1) + Q ^ (N - k) * qbin Q N k := rfl

/-- **Out-of-range vanishing**: `⟨N,k⟩_Q ≈ 0` whenever `k > N`.  By induction
on `N` (each q-Pascal recursion step strictly decreases both indices); stated up
to `Q'.eqv` since `Q'.mul`/`Q'.add` by `0` is only semantically (not
structurally) zero. -/
theorem qbin_out_of_range (Q : Q') : ∀ (N k : Nat), N < k → qbin Q N k ≈ (0 : Q') := by
  intro N
  induction N with
  | zero =>
      intro k hk
      cases k with
      | zero => exact absurd hk (by omega)
      | succ j => exact eqv_refl _  -- qbin Q 0 (j+1) = 0 structurally
  | succ M ih =>
      intro k hk
      cases k with
      | zero => exact absurd hk (by omega)
      | succ j =>
          rw [qbin_succ_succ]
          have hMj1 : M < j + 1 := by omega
          have hMj  : M < j := by omega
          -- qbin Q M (j+1) ≈ 0 and qbin Q M j ≈ 0, so 0 + Q^(M-j)·0 ≈ 0.
          calc qbin Q M (j + 1) + Q ^ (M - j) * qbin Q M j
              ≈ (0 : Q') + Q ^ (M - j) * (0 : Q') :=
                add_eqv_congr _ _ _ _ (ih (j+1) hMj1)
                  (mul_eqv_congr_left _ _ _ (ih j hMj))
            _ ≈ (0 : Q') + (0 : Q') := add_eqv_congr_left _ _ _ (mul_zero_eqv _)
            _ ≈ (0 : Q') := by rw [add_zero']; exact eqv_refl _

/-! ## The product side `∏_{j=1}^{N} (1 + z·q^{2j−1})`

Recursive `def`; `qProd z q (N+1) = qProd z q N · (1 + z·q^{2N+1})`.
The exponent `2j−1` at `j = N+1` is `2N+1`. -/

/-- The Gauss product `∏_{j=1}^{N} (1 + z·q^{2j−1})` as a `Q'` value.
`qProd z q 0 = 1` (empty product); the factor at step `N+1` (i.e. `j = N+1`)
is `1 + z·q^{2N+1}`. -/
def qProd (z q : Q') : Nat → Q'
  | 0     => 1
  | N+1   => qProd z q N * (1 + z * q ^ (2 * N + 1))

@[simp] theorem qProd_zero (z q : Q') : qProd z q 0 = 1 := rfl
@[simp] theorem qProd_succ (z q : Q') (N : Nat) :
    qProd z q (N+1) = qProd z q N * (1 + z * q ^ (2 * N + 1)) := rfl

/-! ## The sum side `Σ_{k=0}^{N} q^{k²}·⟨N,k⟩_{q²}·z^k`

Built as a finite running sum.  The summand at index `k`, for a *fixed* upper
bound `N`, is `gaussTerm z q N k = q^{k²}·⟨N,k⟩_{q²}·z^k`.  The full sum is the
running sum `Σ_{k=0}^{N}`. -/

/-- The `k`-th summand `q^{k²}·⟨N,k⟩_{q²}·z^k` of the Gauss sum (base `Q = q·q`). -/
def gaussTerm (z q : Q') (N k : Nat) : Q' :=
  q ^ (k * k) * qbin (q * q) N k * z ^ k

/-- The finite Gauss sum `Σ_{k=0}^{M} q^{k²}·⟨N,k⟩_{q²}·z^k` (running sum up to
index `M`, with binomials at fixed upper bound `N`).  `gaussSum z q N N` is the
full identity's right-hand side. -/
def gaussSumUpto (z q : Q') (N : Nat) : Nat → Q'
  | 0     => gaussTerm z q N 0
  | M+1   => gaussSumUpto z q N M + gaussTerm z q N (M+1)

@[simp] theorem gaussSumUpto_zero (z q : Q') (N : Nat) :
    gaussSumUpto z q N 0 = gaussTerm z q N 0 := rfl
@[simp] theorem gaussSumUpto_succ (z q : Q') (N M : Nat) :
    gaussSumUpto z q N (M+1) = gaussSumUpto z q N M + gaussTerm z q N (M+1) := rfl

/-- The full Gauss sum `Σ_{k=0}^{N} q^{k²}·⟨N,k⟩_{q²}·z^k`. -/
def gaussSum (z q : Q') (N : Nat) : Q' := gaussSumUpto z q N N

/-! ## Power-arithmetic helpers on `Q'`

`q^a · q^b ≈ q^{a+b}` and the specific exponent identity feeding the
`z·q^{2N+1}` shift.  Proved purely from `Q'.pow_succ`/`pow_zero` (`rfl`s) and
the ring layer; `Nat`-exponent arithmetic is handled by `Nat.add`/`omega`-free
rewrites. -/

/-- `q^a · q^b ≈ q^{a+b}`.  Induction on `b` over the `pow_succ` `rfl`. -/
theorem pow_add_eqv (q : Q') (a b : Nat) : q ^ a * q ^ b ≈ q ^ (a + b) := by
  induction b with
  | zero =>
      -- q^a * q^0 = q^a * 1 ≈ q^a = q^(a+0)
      calc q ^ a * q ^ 0 ≈ q ^ a * 1 := eqv_refl _
        _ ≈ q ^ a := mul_one_eqv _
        _ ≈ q ^ (a + 0) := by rw [Nat.add_zero]; exact eqv_refl _
  | succ b ih =>
      -- q^a * q^(b+1) = q^a * (q * q^b) ≈ q * (q^a * q^b) ≈ q * q^(a+b) = q^(a+b+1) = q^(a+(b+1))
      calc q ^ a * q ^ (b + 1)
          ≈ q ^ a * (q * q ^ b) := by rw [Q'.pow_succ]; exact eqv_refl _
        _ ≈ (q ^ a * q) * q ^ b := eqv_symm (mul_assoc_eqv _ _ _)
        _ ≈ (q * q ^ a) * q ^ b := mul_eqv_congr_right _ _ _ (mul_comm_eqv _ _)
        _ ≈ q * (q ^ a * q ^ b) := mul_assoc_eqv _ _ _
        _ ≈ q * q ^ (a + b) := mul_eqv_congr_left _ _ _ ih
        _ ≈ q ^ (a + b + 1) := by rw [Q'.pow_succ]; exact eqv_refl _
        _ ≈ q ^ (a + (b + 1)) := by rw [Nat.add_succ]; exact eqv_refl _

/-! ## The Gauss-sum step identity (the combinatorial heart)

`gaussSum_step : gaussSum z q N · (1 + z·q^{2N+1}) ≈ gaussSum z q (N+1)`.

This is the entire algebraic content of Gauss's identity once the product
recursion is peeled off.  It is proved by relating the running sums
`gaussSumUpto z q N` and `gaussSumUpto z q (N+1)` via the q-Pascal split.

We prove a stronger *running* statement first, by induction on the running
bound `M`: for `M ≤ N`,

    gaussSumUpto z q N M · 1  +  (z·q^{2N+1})·(prefix shift)  ≈  gaussSumUpto z q (N+1) M  +  tail,

assembled so that at `M = N` the boundary terms close.  Concretely we show, by
induction on `M`, the exact running identity

    gaussSumUpto z q N M  +  z·q^{2N+1}·(running shift over k≤M)
        ≈  gaussSumUpto z q (N+1) M  +  gaussTerm z q (N+1) (M+1) · [overshoot]

— but the clean closing form below avoids carrying an overshoot by splitting
the multiplied sum directly.  See `gaussSum_step`. -/

/-- The "shift contribution": `z·q^{2N+1}` times the `k`-th Gauss term at upper
bound `N` equals the `(k+1)`-th Gauss term at upper bound `N+1` *coming from the
second q-Pascal branch* — i.e. `z·q^{2N+1}·gaussTerm z q N k ≈
q^{(k+1)²}·(Q^{N−k}·⟨N,k⟩)·z^{k+1}` with `Q = q·q`.  This is the exponent
bookkeeping `k² + (2N+1) = (k+1)² + 2(N−k)` (valid for `k ≤ N`). -/
theorem shift_term_eqv (z q : Q') (N k : Nat) (hk : k ≤ N) :
    (z * q ^ (2 * N + 1)) * gaussTerm z q N k
      ≈ q ^ ((k+1) * (k+1)) * ((q * q) ^ (N - k) * qbin (q * q) N k) * z ^ (k + 1) := by
  -- gaussTerm z q N k = q^{k²} * ⟨N,k⟩ * z^k
  -- LHS = z·q^{2N+1} · (q^{k²} · ⟨N,k⟩ · z^k)
  -- We regroup all q-powers together, all z-powers together.
  -- q-power total: q^{2N+1} · q^{k²} ≈ q^{2N+1+k²}.
  -- z-power total: z · z^k = z^{k+1}.
  -- Target q-power: q^{(k+1)²} · (q·q)^{N−k} = q^{(k+1)²} · q^{2(N−k)} ≈ q^{(k+1)²+2(N−k)}.
  -- Exponent identity: 2N+1+k² = (k+1)²+2(N−k), i.e. 2N+1+k² = k²+2k+1+2N−2k = k²+2N+1. ✓
  unfold gaussTerm
  -- First, (q·q)^{N−k} ≈ q^{2(N−k)} as a q-power.
  have hQpow : (q * q) ^ (N - k) ≈ q ^ (2 * (N - k)) := by
    -- (q·q)^m ≈ q^{2m}, induction on m via pow_succ + pow_add_eqv
    induction (N - k) with
    | zero => calc (q * q) ^ 0 ≈ (1 : Q') := eqv_refl _
                _ ≈ q ^ (2 * 0) := by rw [Nat.mul_zero]; exact eqv_refl _
    | succ m ih =>
        -- (q·q)^{m+1} = (q·q)·(q·q)^m ≈ (q·q)·q^{2m} ≈ q·(q·q^{2m})
        --   = q·q^{2m+1} = q^{2m+2} = q^{2(m+1)}.  All q-shifts via `pow_succ` (rfl).
        calc (q * q) ^ (m + 1)
            ≈ (q * q) * (q * q) ^ m := by rw [Q'.pow_succ]; exact eqv_refl _
          _ ≈ (q * q) * q ^ (2 * m) := mul_eqv_congr_left _ _ _ ih
          _ ≈ q * (q * q ^ (2 * m)) := mul_assoc_eqv _ _ _
          _ ≈ q * q ^ (2 * m + 1) := by rw [Q'.pow_succ]; exact eqv_refl _
          _ ≈ q ^ (2 * m + 1 + 1) := by rw [Q'.pow_succ]; exact eqv_refl _
          _ ≈ q ^ (2 * (m + 1)) := by
              rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]; exact eqv_refl _
  -- The combined q-power on the RHS:  q^{(k+1)²} · q^{2(N−k)} ≈ q^{(k+1)²+2(N−k)}.
  -- The combined q-power on the LHS:  q^{2N+1} · q^{k²} ≈ q^{2N+1+k²}.
  -- These exponents are equal: (k+1)² + 2(N−k) = 2N+1 + k²  (for k ≤ N).
  have hexp : (k + 1) * (k + 1) + 2 * (N - k) = (2 * N + 1) + k * k := by
    have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_one, Nat.one_mul,
          Nat.mul_one]
      omega
    rw [hsq]; omega
  -- Now assemble the chain.  Abbreviate B := ⟨N,k⟩ = qbin (q*q) N k.
  -- LHS = (z·q^{2N+1}) · (q^{k²}·B·z^k)
  -- RHS = q^{(k+1)²} · ((q·q)^{N−k}·B) · z^{k+1}
  calc (z * q ^ (2 * N + 1)) * (q ^ (k * k) * qbin (q * q) N k * z ^ k)
      -- pull z to the front, group the two q-powers and the B and z^k
      ≈ ((q ^ (2 * N + 1) * q ^ (k * k)) * qbin (q * q) N k) * (z * z ^ k) := by
        -- rearrange product of factors {z, q^{2N+1}, q^{k²}, B, z^k}
        calc (z * q ^ (2 * N + 1)) * (q ^ (k * k) * qbin (q * q) N k * z ^ k)
            ≈ (z * q ^ (2 * N + 1)) * (q ^ (k * k) * (qbin (q * q) N k * z ^ k)) :=
              mul_eqv_congr_left _ _ _ (mul_assoc_eqv _ _ _)
          _ ≈ ((z * q ^ (2 * N + 1)) * q ^ (k * k)) * (qbin (q * q) N k * z ^ k) :=
              eqv_symm (mul_assoc_eqv _ _ _)
          _ ≈ ((q ^ (2 * N + 1) * z) * q ^ (k * k)) * (qbin (q * q) N k * z ^ k) :=
              mul_eqv_congr_right _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv _ _))
          _ ≈ (q ^ (2 * N + 1) * (z * q ^ (k * k))) * (qbin (q * q) N k * z ^ k) :=
              mul_eqv_congr_right _ _ _ (mul_assoc_eqv _ _ _)
          _ ≈ (q ^ (2 * N + 1) * (q ^ (k * k) * z)) * (qbin (q * q) N k * z ^ k) :=
              mul_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ (mul_comm_eqv _ _))
          _ ≈ ((q ^ (2 * N + 1) * q ^ (k * k)) * z) * (qbin (q * q) N k * z ^ k) :=
              mul_eqv_congr_right _ _ _ (eqv_symm (mul_assoc_eqv _ _ _))
          _ ≈ (q ^ (2 * N + 1) * q ^ (k * k)) * (z * (qbin (q * q) N k * z ^ k)) :=
              mul_assoc_eqv _ _ _
          _ ≈ (q ^ (2 * N + 1) * q ^ (k * k)) * ((z * qbin (q * q) N k) * z ^ k) :=
              mul_eqv_congr_left _ _ _ (eqv_symm (mul_assoc_eqv _ _ _))
          _ ≈ (q ^ (2 * N + 1) * q ^ (k * k)) * ((qbin (q * q) N k * z) * z ^ k) :=
              mul_eqv_congr_left _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv _ _))
          _ ≈ (q ^ (2 * N + 1) * q ^ (k * k)) * (qbin (q * q) N k * (z * z ^ k)) :=
              mul_eqv_congr_left _ _ _ (mul_assoc_eqv _ _ _)
          _ ≈ ((q ^ (2 * N + 1) * q ^ (k * k)) * qbin (q * q) N k) * (z * z ^ k) :=
              eqv_symm (mul_assoc_eqv _ _ _)
    -- collapse the two q-powers and rewrite z·z^k = z^{k+1}
    _ ≈ (q ^ ((2 * N + 1) + k * k) * qbin (q * q) N k) * z ^ (k + 1) := by
        refine mul_eqv_congr _ _ _ _ ?_ ?_
        · exact mul_eqv_congr_right _ _ _ (pow_add_eqv q (2 * N + 1) (k * k))
        · rw [Q'.pow_succ]; exact eqv_refl _
    -- rewrite the exponent and split back into q^{(k+1)²}·q^{2(N−k)}
    _ ≈ (q ^ ((k + 1) * (k + 1) + 2 * (N - k)) * qbin (q * q) N k) * z ^ (k + 1) := by
        rw [hexp]; exact eqv_refl _
    _ ≈ ((q ^ ((k + 1) * (k + 1)) * q ^ (2 * (N - k))) * qbin (q * q) N k) * z ^ (k + 1) :=
        mul_eqv_congr_right _ _ _
          (mul_eqv_congr_right _ _ _ (eqv_symm (pow_add_eqv q ((k+1)*(k+1)) (2*(N-k)))))
    _ ≈ ((q ^ ((k + 1) * (k + 1)) * (q * q) ^ (N - k)) * qbin (q * q) N k) * z ^ (k + 1) :=
        mul_eqv_congr_right _ _ _
          (mul_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ (eqv_symm hQpow)))
    -- reassociate to the target grouping  q^{(k+1)²} · ((q·q)^{N−k}·B) · z^{k+1}
    _ ≈ q ^ ((k + 1) * (k + 1)) * ((q * q) ^ (N - k) * qbin (q * q) N k) * z ^ (k + 1) :=
        mul_eqv_congr_right _ _ _ (mul_assoc_eqv _ _ _)

/-! ### The running step identity

For `M ≤ N`, multiplying the running sum `gaussSumUpto z q N M` by
`(1 + z·q^{2N+1})` and using the q-Pascal split of `gaussTerm z q (N+1) (k+1)`
yields `gaussSumUpto z q (N+1) (M+1)` minus the "missing" `k=0` first-branch
term `gaussTerm z q (N+1) 0`.  We package the closing form directly at the full
bound. -/

/-- The q-Pascal split of a Gauss term at upper bound `N+1`, index `k+1`:
`gaussTerm z q (N+1) (k+1) ≈ gaussTerm z q N (k+1) + (shift of gaussTerm z q N k)`,
where the shift is `(z·q^{2N+1})·gaussTerm z q N k` (for `k ≤ N`).  This is the
q-Pascal recurrence `⟨N+1,k+1⟩ = ⟨N,k+1⟩ + Q^{N−k}⟨N,k⟩` lifted to the weighted
terms. -/
theorem gaussTerm_pascal (z q : Q') (N k : Nat) (hk : k ≤ N) :
    gaussTerm z q (N+1) (k+1)
      ≈ gaussTerm z q N (k+1) + (z * q ^ (2 * N + 1)) * gaussTerm z q N k := by
  -- gaussTerm z q (N+1) (k+1)
  --   = q^{(k+1)²} · ⟨N+1,k+1⟩ · z^{k+1}
  --   = q^{(k+1)²} · (⟨N,k+1⟩ + Q^{N−k}·⟨N,k⟩) · z^{k+1}    (q-Pascal, Q = q·q)
  --   = q^{(k+1)²}·⟨N,k+1⟩·z^{k+1}  +  q^{(k+1)²}·(Q^{N−k}·⟨N,k⟩)·z^{k+1}
  --   = gaussTerm z q N (k+1)       +  (shift, by shift_term_eqv)
  unfold gaussTerm
  rw [qbin_succ_succ]
  -- LHS = q^{(k+1)²} · (⟨N,k+1⟩ + (q·q)^{N−k}·⟨N,k⟩) · z^{k+1}
  calc q ^ ((k+1) * (k+1)) * (qbin (q * q) N (k+1) + (q * q) ^ (N - k) * qbin (q * q) N k)
          * z ^ (k + 1)
      -- distribute the inner sum across the leading q-power
      ≈ (q ^ ((k+1) * (k+1)) * qbin (q * q) N (k+1)
            + q ^ ((k+1) * (k+1)) * ((q * q) ^ (N - k) * qbin (q * q) N k)) * z ^ (k + 1) :=
        mul_eqv_congr_right _ _ _ (mul_add_eqv _ _ _)
      -- distribute z^{k+1} across the outer sum
    _ ≈ (q ^ ((k+1) * (k+1)) * qbin (q * q) N (k+1)) * z ^ (k + 1)
          + (q ^ ((k+1) * (k+1)) * ((q * q) ^ (N - k) * qbin (q * q) N k)) * z ^ (k + 1) :=
        Cheb.add_mul_eqv _ _ _
      -- first summand IS gaussTerm z q N (k+1); second IS the shift (shift_term_eqv backwards)
    _ ≈ q ^ ((k+1) * (k+1)) * qbin (q * q) N (k+1) * z ^ (k + 1)
          + (z * q ^ (2 * N + 1)) * (q ^ (k * k) * qbin (q * q) N k * z ^ k) :=
        add_eqv_congr_left _ _ _ (eqv_symm (shift_term_eqv z q N k hk))

/-! ### Assembling the step: `gaussSum z q N · (1 + z·q^{2N+1}) ≈ gaussSum z q (N+1)`

We prove the running version by induction on `M` (the running bound), valid for
`M ≤ N`:

    gaussSumUpto z q N M · (1 + z·q^{2N+1})
      ≈  gaussSumUpto z q (N+1) (M+1)  −  gaussTerm z q (N+1) 0  +  gaussTerm z q N 0 · (… )

Rather than carrying signed boundary terms, we use the cleaner *shifted*
running identity: at each `M`, the multiplied prefix equals the prefix of the
`(N+1)`-sum from index `1` up to `M+1`, plus the `1·(k=0)` term.  The full
identity then closes because the top branch of the `(N+1)`-sum at index `N+1`
is supplied by the shift of the index-`N` term. -/

/-- **Running step identity.**  For all `M`, with the q-Pascal split valid up to
`M ≤ N` enforced pointwise by `gaussTerm_pascal`:

    gaussSumUpto z q N M + (z·q^{2N+1}) · gaussSumUpto z q N M
      ≈ gaussSumUpto z q (N+1) M  +  (z·q^{2N+1}) · gaussTerm z q N M  ...

We instead prove the directly-useful identity: the multiplied running sum
telescopes the q-Pascal splits.  Precisely, for `M ≤ N`:

    gaussSumUpto z q N M · (1 + z·q^{2N+1})
      ≈ gaussSumUpto z q (N+1) M + (z·q^{2N+1}) · gaussTerm z q N M.

The right side's first summand is the `(N+1)`-sum prefix up to `M`; the second
is the *pending shift* of the last term, which at the next step becomes the
`(M+1)`-branch's second half. -/
theorem gaussSum_run (z q : Q') (N : Nat) :
    ∀ M, M ≤ N →
      gaussSumUpto z q N M * (1 + z * q ^ (2 * N + 1))
        ≈ gaussSumUpto z q (N+1) M
            + (z * q ^ (2 * N + 1)) * gaussTerm z q N M := by
  intro M
  induction M with
  | zero =>
      intro _
      -- M = 0.  gaussSumUpto _ _ 0 = gaussTerm _ _ 0.
      -- gaussTerm z q N 0 = q^0·⟨N,0⟩·z^0 = 1·1·1 ; gaussTerm z q (N+1) 0 same = 1.
      -- LHS = gaussTerm z q N 0 · (1 + zq^{2N+1})
      --     = gaussTerm z q N 0 + gaussTerm z q N 0 · (z q^{2N+1})
      -- RHS = gaussTerm z q (N+1) 0 + (z q^{2N+1})·gaussTerm z q N 0
      -- Need gaussTerm z q N 0 ≈ gaussTerm z q (N+1) 0  (both equal 1) and a commute.
      show gaussTerm z q N 0 * (1 + z * q ^ (2 * N + 1))
            ≈ gaussTerm z q (N+1) 0 + (z * q ^ (2 * N + 1)) * gaussTerm z q N 0
      have hb : gaussTerm z q (N+1) 0 ≈ gaussTerm z q N 0 := by
        -- both are q^0·1·z^0 with the ⟨·,0⟩ = 1
        unfold gaussTerm
        show q ^ (0 * 0) * qbin (q * q) (N+1) 0 * z ^ 0
              ≈ q ^ (0 * 0) * qbin (q * q) N 0 * z ^ 0
        rw [qbin_succ_zero]
        cases N with
        | zero => exact eqv_refl _
        | succ M => rw [qbin_succ_zero]; exact eqv_refl _
      calc gaussTerm z q N 0 * (1 + z * q ^ (2 * N + 1))
          ≈ gaussTerm z q N 0 * 1 + gaussTerm z q N 0 * (z * q ^ (2 * N + 1)) :=
            mul_add_eqv _ _ _
        _ ≈ gaussTerm z q N 0 + gaussTerm z q N 0 * (z * q ^ (2 * N + 1)) :=
            add_eqv_congr_right _ _ _ (mul_one_eqv _)
        _ ≈ gaussTerm z q (N+1) 0 + (z * q ^ (2 * N + 1)) * gaussTerm z q N 0 :=
            add_eqv_congr _ _ _ _ (eqv_symm hb) (mul_comm_eqv _ _)
  | succ M ih =>
      intro hM
      have hMN : M ≤ N := Nat.le_of_succ_le hM
      -- gaussSumUpto z q N (M+1) = gaussSumUpto z q N M + gaussTerm z q N (M+1)
      -- Distribute (1 + zq^{2N+1}):
      --   = [gaussSumUpto N M · (1+…)]  +  [gaussTerm N (M+1) · (1+…)]
      -- IH handles the first bracket; second bracket splits into
      --   gaussTerm N (M+1)·1 + gaussTerm N (M+1)·(zq^{2N+1}).
      -- Reassemble against RHS at M+1:
      --   gaussSumUpto (N+1) (M+1) + (zq^{2N+1})·gaussTerm N (M+1)
      -- where gaussSumUpto (N+1) (M+1) = gaussSumUpto (N+1) M + gaussTerm (N+1) (M+1),
      -- and gaussTerm (N+1) (M+1) = gaussTerm N (M+1) + (zq^{2N+1})·gaussTerm N M  (gaussTerm_pascal).
      show (gaussSumUpto z q N M + gaussTerm z q N (M+1)) * (1 + z * q ^ (2 * N + 1))
            ≈ gaussSumUpto z q (N+1) (M+1)
                + (z * q ^ (2 * N + 1)) * gaussTerm z q N (M+1)
      -- Notation for the recurring atom W := z·q^{2N+1}.
      let W : Q' := z * q ^ (2 * N + 1)
      show (gaussSumUpto z q N M + gaussTerm z q N (M+1)) * (1 + W)
            ≈ gaussSumUpto z q (N+1) (M+1) + W * gaussTerm z q N (M+1)
      calc (gaussSumUpto z q N M + gaussTerm z q N (M+1)) * (1 + W)
          ≈ gaussSumUpto z q N M * (1 + W) + gaussTerm z q N (M+1) * (1 + W) :=
            Cheb.add_mul_eqv _ _ _
        -- apply IH to the first bracket
        _ ≈ (gaussSumUpto z q (N+1) M + W * gaussTerm z q N M)
              + gaussTerm z q N (M+1) * (1 + W) :=
            add_eqv_congr_right _ _ _ (ih hMN)
        -- expand the second bracket  gaussTerm N (M+1) · 1  +  gaussTerm N (M+1) · W
        _ ≈ (gaussSumUpto z q (N+1) M + W * gaussTerm z q N M)
              + (gaussTerm z q N (M+1) + gaussTerm z q N (M+1) * W) :=
            add_eqv_congr_left _ _ _
              (eqv_trans _ _ _ (mul_add_eqv _ _ _)
                (add_eqv_congr_right _ _ _ (mul_one_eqv _)))
        -- Goal now: regroup into  [gaussSumUpto (N+1) M + gaussTerm (N+1) (M+1)]
        --                          + W·gaussTerm N (M+1)
        -- Use:  gaussTerm (N+1) (M+1) ≈ gaussTerm N (M+1) + W·gaussTerm N M   (gaussTerm_pascal)
        -- The four atoms on the LHS are:
        --   A = gaussSumUpto (N+1) M
        --   B = W·gaussTerm N M
        --   C = gaussTerm N (M+1)
        --   D = gaussTerm N (M+1)·W   (≈ W·gaussTerm N (M+1))
        -- Target:  (A + (C + B)) + (W·gaussTerm N (M+1))
        --        =  (A + gaussTerm (N+1) (M+1)) + W·gaussTerm N (M+1).
        _ ≈ (gaussSumUpto z q (N+1) M + (gaussTerm z q N (M+1) + W * gaussTerm z q N M))
              + W * gaussTerm z q N (M+1) := by
            -- LHS of this step: (A + B) + (C + D).  We want (A + (C + B)) + D'
            -- with D' = W·gaussTerm N (M+1) and D = gaussTerm N (M+1)·W ≈ D'.
            -- First: (A + B) + (C + D) ≈ A + (B + (C + D))  [assoc]
            --        ≈ A + ((B + C) + D) ≈ A + ((C + B) + D)  [comm inner]
            --        ≈ (A + (C + B)) + D  [assoc back]
            --        ≈ (A + (C + B)) + D'  [D ≈ D']
            calc (gaussSumUpto z q (N+1) M + W * gaussTerm z q N M)
                    + (gaussTerm z q N (M+1) + gaussTerm z q N (M+1) * W)
                ≈ gaussSumUpto z q (N+1) M
                    + (W * gaussTerm z q N M
                        + (gaussTerm z q N (M+1) + gaussTerm z q N (M+1) * W)) :=
                  add_assoc_eqv _ _ _
              _ ≈ gaussSumUpto z q (N+1) M
                    + ((W * gaussTerm z q N M + gaussTerm z q N (M+1))
                        + gaussTerm z q N (M+1) * W) :=
                  add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv _ _ _))
              _ ≈ gaussSumUpto z q (N+1) M
                    + ((gaussTerm z q N (M+1) + W * gaussTerm z q N M)
                        + gaussTerm z q N (M+1) * W) :=
                  add_eqv_congr_left _ _ _
                    (add_eqv_congr_right _ _ _ (add_comm_eqv _ _))
              _ ≈ (gaussSumUpto z q (N+1) M
                    + (gaussTerm z q N (M+1) + W * gaussTerm z q N M))
                    + gaussTerm z q N (M+1) * W :=
                  eqv_symm (add_assoc_eqv _ _ _)
              _ ≈ (gaussSumUpto z q (N+1) M
                    + (gaussTerm z q N (M+1) + W * gaussTerm z q N M))
                    + W * gaussTerm z q N (M+1) :=
                  add_eqv_congr_left _ _ _ (mul_comm_eqv _ _)
        -- Now fold (gaussTerm N (M+1) + W·gaussTerm N M) back into gaussTerm (N+1) (M+1).
        _ ≈ (gaussSumUpto z q (N+1) M + gaussTerm z q (N+1) (M+1))
              + W * gaussTerm z q N (M+1) :=
            add_eqv_congr_right _ _ _
              (add_eqv_congr_left _ _ _ (eqv_symm (gaussTerm_pascal z q N M hMN)))
        -- And gaussSumUpto (N+1) M + gaussTerm (N+1) (M+1) = gaussSumUpto (N+1) (M+1).
        _ ≈ gaussSumUpto z q (N+1) (M+1) + W * gaussTerm z q N (M+1) := eqv_refl _

/-- **The Gauss-sum step (boundary-closed).**  `gaussSum z q N · (1 + z·q^{2N+1})
≈ gaussSum z q (N+1)`.  Specialises `gaussSum_run` at the full bound `M = N`:
the pending shift `(z·q^{2N+1})·gaussTerm z q N N` becomes precisely the missing
top term `gaussTerm z q (N+1) (N+1)` of the `(N+1)`-sum (its q-Pascal second
branch, with the first branch `gaussTerm z q N (N+1) = 0` since `⟨N,N+1⟩ = 0`). -/
theorem gaussSum_step (z q : Q') (N : Nat) :
    gaussSum z q N * (1 + z * q ^ (2 * N + 1)) ≈ gaussSum z q (N+1) := by
  unfold gaussSum
  -- gaussSum z q (N+1) = gaussSumUpto z q (N+1) (N+1)
  --   = gaussSumUpto z q (N+1) N + gaussTerm z q (N+1) (N+1).
  -- gaussSum_run at M=N gives:
  --   gaussSumUpto z q N N · (1+…) ≈ gaussSumUpto z q (N+1) N + (z q^{2N+1})·gaussTerm z q N N.
  -- It remains to show  (z q^{2N+1})·gaussTerm z q N N ≈ gaussTerm z q (N+1) (N+1).
  -- By gaussTerm_pascal at k=N:  gaussTerm (N+1)(N+1) ≈ gaussTerm N (N+1) + (zq^{2N+1})·gaussTerm N N.
  -- And gaussTerm N (N+1) = q^{…}·⟨N,N+1⟩·z^{…} with ⟨N,N+1⟩ = 0, so that term ≈ 0.
  have hrun := gaussSum_run z q N N (Nat.le_refl N)
  -- gaussTerm z q N (N+1) ≈ 0  (since ⟨N,N+1⟩ = 0)
  have hzero : gaussTerm z q N (N+1) ≈ (0 : Q') := by
    unfold gaussTerm
    -- gaussTerm = q^{(N+1)²} · ⟨N,N+1⟩ · z^{N+1}, with ⟨N,N+1⟩ ≈ 0.
    have hq0 : qbin (q * q) N (N + 1) ≈ (0 : Q') :=
      qbin_out_of_range (q * q) N (N + 1) (by omega)
    calc q ^ ((N+1) * (N+1)) * qbin (q * q) N (N + 1) * z ^ (N + 1)
        ≈ q ^ ((N+1) * (N+1)) * (0 : Q') * z ^ (N + 1) :=
          mul_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ hq0)
      _ ≈ (0 : Q') * z ^ (N + 1) :=
          mul_eqv_congr_right _ _ _ (mul_zero_eqv _)
      _ ≈ (0 : Q') := zero_mul_eqv _
  -- gaussTerm z q (N+1) (N+1) ≈ (z q^{2N+1})·gaussTerm z q N N
  have hpasc : gaussTerm z q (N+1) (N+1)
        ≈ (z * q ^ (2 * N + 1)) * gaussTerm z q N N := by
    calc gaussTerm z q (N+1) (N+1)
        ≈ gaussTerm z q N (N+1) + (z * q ^ (2 * N + 1)) * gaussTerm z q N N :=
          gaussTerm_pascal z q N N (Nat.le_refl N)
      _ ≈ (0 : Q') + (z * q ^ (2 * N + 1)) * gaussTerm z q N N :=
          add_eqv_congr_right _ _ _ hzero
      _ ≈ (z * q ^ (2 * N + 1)) * gaussTerm z q N N := by
          rw [zero_add']; exact eqv_refl _
  -- Assemble:  LHS ≈ gaussSumUpto (N+1) N + (zq^{2N+1})·gaussTerm N N
  --                ≈ gaussSumUpto (N+1) N + gaussTerm (N+1) (N+1)
  --                = gaussSumUpto (N+1) (N+1).
  calc gaussSumUpto z q N N * (1 + z * q ^ (2 * N + 1))
      ≈ gaussSumUpto z q (N+1) N + (z * q ^ (2 * N + 1)) * gaussTerm z q N N := hrun
    _ ≈ gaussSumUpto z q (N+1) N + gaussTerm z q (N+1) (N+1) :=
        add_eqv_congr_left _ _ _ (eqv_symm hpasc)
    _ ≈ gaussSumUpto z q (N+1) (N+1) := eqv_refl _

/-! ## The main identity, by induction on `N` -/

/-- **Base case** `N = 0`: `qProd z q 0 ≈ gaussSum z q 0`, i.e. `1 ≈ 1`
(empty product equals the single `k=0` term `q^0·⟨0,0⟩·z^0 = 1`). -/
theorem gauss_qbinom_base (z q : Q') : qProd z q 0 ≈ gaussSum z q 0 := by
  show (1 : Q') ≈ gaussSumUpto z q 0 0
  show (1 : Q') ≈ gaussTerm z q 0 0
  -- gaussTerm z q 0 0 = q^0·⟨0,0⟩·z^0 = 1·1·1
  unfold gaussTerm
  show (1 : Q') ≈ q ^ (0 * 0) * qbin (q * q) 0 0 * z ^ 0
  -- q^0 = 1, ⟨0,0⟩ = 1, z^0 = 1
  show (1 : Q') ≈ (1 : Q') * (1 : Q') * (1 : Q')
  calc (1 : Q') ≈ (1 : Q') * (1 : Q') := eqv_symm (mul_one_eqv _)
    _ ≈ ((1 : Q') * (1 : Q')) * (1 : Q') := eqv_symm (mul_one_eqv _)

/-- **The inductive step.**  `qProd z q N ≈ gaussSum z q N`
`⟹ qProd z q (N+1) ≈ gaussSum z q (N+1)`.  Multiply the product recursion by
the new factor and apply `gaussSum_step`. -/
theorem gauss_qbinom_step (z q : Q') (N : Nat)
    (ih : qProd z q N ≈ gaussSum z q N) :
    qProd z q (N+1) ≈ gaussSum z q (N+1) := by
  -- qProd z q (N+1) = qProd z q N · (1 + z·q^{2N+1})
  show qProd z q N * (1 + z * q ^ (2 * N + 1)) ≈ gaussSum z q (N+1)
  calc qProd z q N * (1 + z * q ^ (2 * N + 1))
      ≈ gaussSum z q N * (1 + z * q ^ (2 * N + 1)) :=
        mul_eqv_congr_right _ _ _ ih
    _ ≈ gaussSum z q (N+1) := gaussSum_step z q N

/-- **Gauss's q-binomial identity, CLOSED for all `N`.**  For arbitrary
`Q'`-parameters `z, q` and every `N`:

    ∏_{j=1}^{N} (1 + z·q^{2j−1})  ≈  Σ_{k=0}^{N} q^{k²}·⟨N,k⟩_{q²}·z^k,

i.e. `qProd z q N ≈ gaussSum z q N`.  Proved by induction on `N` via the
q-Pascal recurrence (`gaussSum_step`).  This is the Gaussian-theta-weight
analogue of `UTelescope.uTelescope_all`. -/
theorem gauss_qbinom_all (z q : Q') : ∀ N, qProd z q N ≈ gaussSum z q N := by
  intro N
  induction N with
  | zero => exact gauss_qbinom_base z q
  | succ k ih => exact gauss_qbinom_step z q k ih

end YMGap.Continuum.GaussQBinom

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only via the reused `Int`/`omega` helpers in the `Q'` base
layer) — never `Classical.*`, `sorryAx`, or `native_decide`. -/

#print axioms YMGap.Continuum.GaussQBinom.qbin_succ_succ
#print axioms YMGap.Continuum.GaussQBinom.qbin_out_of_range
#print axioms YMGap.Continuum.GaussQBinom.pow_add_eqv
#print axioms YMGap.Continuum.GaussQBinom.shift_term_eqv
#print axioms YMGap.Continuum.GaussQBinom.gaussTerm_pascal
#print axioms YMGap.Continuum.GaussQBinom.gaussSum_run
#print axioms YMGap.Continuum.GaussQBinom.gaussSum_step
#print axioms YMGap.Continuum.GaussQBinom.gauss_qbinom_base
#print axioms YMGap.Continuum.GaussQBinom.gauss_qbinom_step
#print axioms YMGap.Continuum.GaussQBinom.gauss_qbinom_all
