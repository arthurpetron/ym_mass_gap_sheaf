/-
# The Chebyshev-U generating-function partial-sum identity — the load-bearing tool
# for the heat-kernel `κ = Σ_f r_f U_f` expansion, plus the honest map of the
# residual to `ChebRProjection.RTruncTail`.

This module proves, π-free and axiom-clean over `Q'`, the foundational
**Chebyshev-U generating-function partial-sum (telescoping) identity**

    factor(c,x)·(Σ_{n<N+1} cⁿ Uₙ(x))  ≈  1 − ( c^{N+1}·U_{N+1}(x) − c^{N+2}·U_N(x) ),
    factor(c,x) := 1 − 2 c x + c²,                                            (GF)

the finite, exact form of the classical generating function
`1/(1 − 2cx + c²) = Σ_n cⁿ Uₙ(x)` (read as `factor·(partial sum) = 1 − tail`).
The single algebraic engine is the second-kind recurrence
`U_{n+2}(x) = 2x·U_{n+1}(x) − Uₙ(x)` (`ChebyshevBound.U_succ_succ`); the proof is
a clean two-term telescope.

This is exactly the per-node U-generating function that `UsumFactorization` NAMES
(the `usumConv` field of `FactoredNodes`, and the prose
`factor_k(z)·Σ_n Uₙ(x_k) zⁿ = 1`) but does NOT prove as a standalone partial-sum
telescope — here it is PROVED, general `N`, `c`, `x`.

## The honest map of the deep target `κ = Σ_f r_f U_f`

The proved-nonnegative node kernel is `κ = R = ϑ₃·S` (`ChebyshevQuadPSD.kappa`),
where `ϑ₃` is a convergent `CReal` **product** (`ThetaConvGen.thetaConvCRealGen`,
via `Ppart`/`prodUp`) and `S = Σ_n sTerm` is a convergent sum whose `n`-th term is
the Poisson-type `2·a^{2n+1}/(1 + 2 a^{2n+1} x + a^{2(2n+1)})`
(`HeatKernelConv.sTerm`).  Note `sTerm`'s denominator is `1 + 2cx + c²`, i.e.
`factor(c, −x)`, so each `S`-term is `Σ_n (−c)ⁿ Uₙ(x)` via (GF) — the generating
function applies per term.

The K_t-side series `R = 2·Σ_n dTerm`, `dTerm a x n = (n+1)·a^{(n+1)²}·Uₙ(x)`
(`JTPIdentity.dPartial`), has its U-coefficients `r_f = rCoeff a f = 2(f+1)a^{(f+1)²}`
BUILT IN by definition (`RCoeffReproduction.rCoeff`).  Thus `κ = Σ_f r_f U_f` is the
identity `ϑ₃·S = 2·Σ dTerm`, i.e. the differentiated Jacobi triple product
`K_t = R` — which the codebase already names as the deep open analytic atom
`JTPIdentity.DiffJTP`.  We do NOT re-fake that.

What IS reducible per edge is the truncation tail under the orthogonality integral:
`ChebRProjection.RTruncTail a` (`∫U_e R √ ≃ ∫U_e R_{e+1} √`), already strictly
smaller than `RProjection a`, with `rProjection_of_tail` the proved reduction.  We
expose the precise place where (GF) feeds that route: (GF) is the per-`S`-term
U-expansion that, summed, yields the `Σ_f r_f U_f` head against which the truncated
orthogonality integral is computed.

## PROVED here (axiom-clean, π-free)

  * `Gpart` — the partial generating sum `Σ_{n<N} cⁿ Uₙ(x)`.
  * `factorC` — the Poisson factor `1 − 2cx + c²` as a `Q'` value.
  * `gf_telescope` — **(GF)**, general `N`, by induction on the recurrence.
  * `gf_step` — the single-step telescoping core
    `factor·(c^{N+1} U_{N+1}) ≈ tail N − tail (N+1)`.
  * `factorC_eq_eval` — `factorC c x ≈ eval (UsumFactorization.factor x) c`
    (consistency with the existing node-factor polynomial machinery).

## NAMED-open (honestly, the deep atoms — NOT touched/faked)

  * `JTPIdentity.DiffJTP` — the differentiated-JTP identity `κ = Σ r_f U_f`
    (= `ϑ₃·S = 2 Σ dTerm`), the genuine analytic wall.
  * `ChebRProjection.RTruncTail a` — the per-edge integral truncation tail
    (already the strictly-smaller reduced atom; `rProjection_of_tail` proved).

## Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorry`/`sorryAx`,
no `native_decide`, no new `axiom`.  `decide` only on closed `Q'`/`Nat`.
-/

import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.UsumFactorization
import YMGap.Constructive.QPoly
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.ChebHeatKernelExpansion

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.QPoly (q_add_zero_eqv q_zero_add_eqv)
open YMGap.Continuum.Cheb (U U_zero U_one U_succ_succ add_eqv_congr)

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 1. The Poisson factor and the partial generating sum -/

/-- The Poisson / Chebyshev-U generating factor `factor(c,x) = 1 − 2cx + c²` as a
`Q'` value, kept additively as `(1 + c·c) + (−(2·c·x))`. -/
def factorC (c x : Q') : Q' := (1 + c * c) + (-(((2 : Q') * c) * x))

/-- The partial generating sum `Gpart c x N = Σ_{n<N} cⁿ Uₙ(x)`. -/
def Gpart (c x : Q') : Nat → Q'
  | 0 => 0
  | (N + 1) => Gpart c x N + (c ^ N * U N x)

@[simp] theorem Gpart_zero (c x : Q') : Gpart c x 0 = 0 := rfl
@[simp] theorem Gpart_succ (c x : Q') (N : Nat) :
    Gpart c x (N + 1) = Gpart c x N + (c ^ N * U N x) := rfl

/-- The telescoping **tail** `tail c x N = c^{N+1}·U_{N+1}(x) − c^{N+2}·U_N(x)`,
kept additively. -/
def tailG (c x : Q') (N : Nat) : Q' :=
  (c ^ (N + 1) * U (N + 1) x) + (-(c ^ (N + 2) * U N x))

/-! ## 2. Consistency with the existing node-factor polynomial `UsumFactorization.factor`

`UsumFactorization.factor x = [1, −2x, 1]` and `eval [1,−2x,1] c = (1 + c²) + (−(2x))·c`
(`UsumFactorization.eval_factor`).  Our `factorC c x = (1 + c²) + (−(2c))·x` is the
same value (just `c`/`x` written in the symmetric order `2cx`). -/

/-- `factorC c x ≈ eval (UsumFactorization.factor x) c`.  Both are `1 − 2cx + c²`;
the only difference is `(−(2c))·x` vs `(−(2x))·c`, equal by commutativity. -/
theorem factorC_eq_eval (c x : Q') :
    factorC c x ≈ QPoly.eval (UsumFactorization.factor x) c := by
  refine eqv_trans _ _ _ ?_ (eqv_symm (UsumFactorization.eval_factor x c))
  show (1 + c * c) + (-(((2 : Q') * c) * x)) ≈ (1 + c * c) + (-(((2 : Q') * x))) * c
  refine add_eqv_congr_left _ _ _ ?_
  -- -(2c·x) ≈ (-(2x))·c
  -- -(2c·x) ≈ -((2x)·c)  [since 2c·x ≈ 2x·c]  ≈ (-(2x))·c  [neg_mul]
  refine eqv_trans _ _ _ (neg_eqv_congr _ _ ?_) (eqv_symm (neg_mul_eqv ((2 : Q') * x) c))
  -- (2c)·x ≈ (2x)·c
  refine eqv_trans _ _ _ (mul_assoc_eqv (2 : Q') c x) ?_
  refine eqv_trans _ _ _ (mul_eqv_congr_left (2 : Q') _ _ (mul_comm_eqv c x)) ?_
  exact eqv_symm (mul_assoc_eqv (2 : Q') x c)

/-! ## 3. The single-step telescoping core

`factorC·(c^{N+1}·U_{N+1}) ≈ tailG N − tailG (N+1)`.  Expanding
`factorC = 1 + c² − 2cx`:

  factorC·(c^{N+1}U_{N+1})
    = c^{N+1}U_{N+1} + c^{N+3}U_{N+1} − 2cx·c^{N+1}U_{N+1}
    = c^{N+1}U_{N+1} + c^{N+3}U_{N+1} − c^{N+2}·(2x·U_{N+1}).

  tailG N − tailG (N+1)
    = c^{N+1}U_{N+1} − c^{N+2}U_N − c^{N+2}U_{N+2} + c^{N+3}U_{N+1}.

These agree iff `c^{N+2}·(2x·U_{N+1}) = c^{N+2}U_N + c^{N+2}U_{N+2}`, i.e.
`2x·U_{N+1} = U_N + U_{N+2}`, the recurrence `U_{N+2} = 2x·U_{N+1} − U_N`. -/

/-- Power bookkeeping: `c^{N+1} ≈ c^{N+2} · ...`? — the explicit powers we use.
`c^{N+2} ≈ c^{N+1}·c` and `c^{N+3} ≈ c^{N+1}·(c·c)`. -/
theorem cpow_n2 (c : Q') (N : Nat) : c ^ (N + 2) ≈ (c ^ (N + 1)) * c := by
  -- c^(N+2) = c·c^(N+1) ; reorder to c^(N+1)·c
  show c * c ^ (N + 1) ≈ (c ^ (N + 1)) * c
  exact mul_comm_eqv c (c ^ (N + 1))

theorem cpow_n3 (c : Q') (N : Nat) : c ^ (N + 3) ≈ (c ^ (N + 1)) * (c * c) := by
  -- c^(N+3) = c·c^(N+2) = c·(c·c^(N+1))
  show c * c ^ (N + 2) ≈ (c ^ (N + 1)) * (c * c)
  show c * (c * c ^ (N + 1)) ≈ (c ^ (N + 1)) * (c * c)
  -- c·(c·p) ≈ p·(c·c)  with p = c^(N+1)
  refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv c c (c ^ (N + 1)))) ?_
  -- (c·c)·p ≈ p·(c·c)
  exact mul_comm_eqv (c * c) (c ^ (N + 1))

/-- **The single-step telescoping core.**  `factorC c x · (c^{N+1}·U_{N+1}(x))
≈ tailG c x N + (−(tailG c x (N+1)))`.

Both sides are normalised to the canonical three-term form
`A + (B + (−C))` with
`A := c^{N+1}·U_{N+1}`,  `B := c^{N+1}·(c·c)·U_{N+1}`,
`C := c^{N+1}·c·(2x·U_{N+1})`; the recurrence `U_N + U_{N+2} = 2x·U_{N+1}` collapses
the two negative tail terms of the RHS into `−C`. -/
theorem gf_step (c x : Q') (N : Nat) :
    factorC c x * (c ^ (N + 1) * U (N + 1) x)
      ≈ tailG c x N + (-(tailG c x (N + 1))) := by
  -- Abbreviations (kept inline): p := c^(N+1), u1 := U_{N+1}, u0 := U N, u2 := U_{N+2}.
  -- Canonical targets:
  --   A := p * u1
  --   B := (p * (c*c)) * u1
  --   C := (p * c) * ((2x) * u1)
  -- We prove LHS ≈ A + (B + (-C))  and  RHS ≈ A + (B + (-C)).
  -- === LHS ≈ A + (B + (-C)) ===
  have hL : factorC c x * (c ^ (N + 1) * U (N + 1) x)
      ≈ (c ^ (N + 1) * U (N + 1) x)
        + (((c ^ (N + 1) * (c * c)) * U (N + 1) x)
          + (-((c ^ (N + 1) * c) * (((2 : Q') * x) * U (N + 1) x)))) := by
    -- factorC = (1 + c*c) + (-(2c·x))
    -- factorC·(p·u1) = (1+c²)·(p·u1) + (-(2cx))·(p·u1)
    refine eqv_trans _ _ _
      (add_mul_eqv (1 + c * c) (-(((2:Q')*c)*x)) (c ^ (N + 1) * U (N + 1) x)) ?_
    -- term 1: (1+c²)·(p·u1) ≈ p·u1 + (p·(c·c))·u1
    have ht1' : (1 + c * c) * (c ^ (N + 1) * U (N + 1) x)
        ≈ (c ^ (N + 1) * U (N + 1) x) + ((c ^ (N + 1) * (c * c)) * U (N + 1) x) := by
      -- (1+c²)·V ≈ 1·V + (c·c)·V ≈ V + (c·c)·V
      refine eqv_trans _ _ _ (add_mul_eqv 1 (c * c) (c ^ (N + 1) * U (N + 1) x)) ?_
      refine add_eqv_congr _ _ _ _ (one_mul_eqv (c ^ (N + 1) * U (N + 1) x)) ?_
      -- (c·c)·(p·u1) ≈ (p·(c·c))·u1
      refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (c * c) (c ^ (N + 1)) (U (N + 1) x))) ?_
      refine mul_eqv_congr_right _ _ (U (N + 1) x) ?_
      exact mul_comm_eqv (c * c) (c ^ (N + 1))
    -- term 2: (-(2cx))·(p·u1) ≈ -((p·c)·((2x)·u1))
    have ht2 : (-(((2:Q')*c)*x)) * (c ^ (N + 1) * U (N + 1) x)
        ≈ -((c ^ (N + 1) * c) * (((2 : Q') * x) * U (N + 1) x)) := by
      -- (-(2cx))·(p·u1) ≈ -((2cx)·(p·u1)) ; then (2cx)·(p·u1) ≈ (p·c)·((2x)·u1)
      refine eqv_trans _ _ _ (neg_mul_eqv (((2:Q')*c)*x) (c ^ (N + 1) * U (N + 1) x)) ?_
      refine neg_eqv_congr _ _ ?_
      -- Goal: ((2c)·x)·(p·u1) ≈ (p·c)·((2x)·u1).  Both are products of {2,c,x,p,u1}.
      -- Normalise BOTH sides to the canonical form  K := 2·(c·(x·(p·u1))).
      -- p := c^(N+1).
      have hLcanon : (((2:Q')*c)*x) * (c ^ (N + 1) * U (N + 1) x)
          ≈ (2:Q') * (c * (x * (c ^ (N + 1) * U (N + 1) x))) := by
        -- ((2c)·x)·(p·u1) ≈ (2c)·(x·(p·u1)) ≈ (2·(c·(x·(p·u1))))
        refine eqv_trans _ _ _ (mul_assoc_eqv ((2:Q')*c) x (c ^ (N + 1) * U (N + 1) x)) ?_
        exact mul_assoc_eqv (2:Q') c (x * (c ^ (N + 1) * U (N + 1) x))
      have hRcanon : (c ^ (N + 1) * c) * (((2 : Q') * x) * U (N + 1) x)
          ≈ (2:Q') * (c * (x * (c ^ (N + 1) * U (N + 1) x))) := by
        -- (p·c)·((2x)·u1) ≈ (p·c)·(2·(x·u1))  [assoc inner]
        refine eqv_trans _ _ _
          (mul_eqv_congr_left (c ^ (N + 1) * c) _ _ (mul_assoc_eqv (2:Q') x (U (N + 1) x))) ?_
        -- (p·c)·(2·(x·u1)) ≈ 2·((p·c)·(x·u1))   [pull 2 out: a·(2·b) ≈ 2·(a·b)]
        refine eqv_trans _ _ _
          (eqv_symm (mul_assoc_eqv (c ^ (N + 1) * c) (2:Q') (x * U (N + 1) x))) ?_
        refine eqv_trans _ _ _
          (mul_eqv_congr_right _ _ (x * U (N + 1) x) (mul_comm_eqv (c ^ (N + 1) * c) (2:Q'))) ?_
        refine eqv_trans _ _ _ (mul_assoc_eqv (2:Q') (c ^ (N + 1) * c) (x * U (N + 1) x)) ?_
        -- 2·((p·c)·(x·u1)) ≈ 2·(c·(x·(p·u1)))
        refine mul_eqv_congr_left (2:Q') _ _ ?_
        -- (p·c)·(x·u1) ≈ c·(x·(p·u1))
        -- (p·c)·(x·u1) ≈ p·(c·(x·u1))  [assoc]
        refine eqv_trans _ _ _ (mul_assoc_eqv (c ^ (N + 1)) c (x * U (N + 1) x)) ?_
        -- p·(c·(x·u1)) ≈ c·(x·(p·u1)) : move p inside past c and x
        -- p·(c·(x·u1)) ≈ c·(p·(x·u1))  [a·(c·Y) ≈ c·(a·Y)]
        refine eqv_trans _ _ _
          (eqv_symm (mul_assoc_eqv (c ^ (N + 1)) c (x * U (N + 1) x))) ?_
        refine eqv_trans _ _ _
          (mul_eqv_congr_right _ _ (x * U (N + 1) x) (mul_comm_eqv (c ^ (N + 1)) c)) ?_
        refine eqv_trans _ _ _ (mul_assoc_eqv c (c ^ (N + 1)) (x * U (N + 1) x)) ?_
        refine mul_eqv_congr_left c _ _ ?_
        -- p·(x·u1) ≈ x·(p·u1)
        refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv (c ^ (N + 1)) x (U (N + 1) x))) ?_
        refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ (U (N + 1) x) (mul_comm_eqv (c ^ (N + 1)) x)) ?_
        exact mul_assoc_eqv x (c ^ (N + 1)) (U (N + 1) x)
      exact eqv_trans _ _ _ hLcanon (eqv_symm hRcanon)
    -- assemble: term1 + term2 ≈ A + (B + (-C))
    refine eqv_trans _ _ _ (add_eqv_congr _ _ _ _ ht1' ht2) ?_
    -- (A + B) + (-C) ≈ A + (B + (-C))
    exact add_assoc_eqv (c ^ (N + 1) * U (N + 1) x)
      ((c ^ (N + 1) * (c * c)) * U (N + 1) x)
      (-((c ^ (N + 1) * c) * (((2 : Q') * x) * U (N + 1) x)))
  -- === RHS ≈ A + (B + (-C)) ===
  -- tailG N = c^{N+1}u1 + (-(c^{N+2}·u0))
  -- tailG (N+1) = c^{N+2}·u2 + (-(c^{N+3}·u1))
  -- -tailG(N+1) = (-(c^{N+2}·u2)) + (c^{N+3}·u1)
  -- RHS = (A + (-(c^{N+2}u0))) + ((-(c^{N+2}u2)) + (c^{N+3}u1))
  -- Substitute c^{N+2} ≈ p·c, c^{N+3} ≈ p·(c·c).
  have hR : tailG c x N + (-(tailG c x (N + 1)))
      ≈ (c ^ (N + 1) * U (N + 1) x)
        + (((c ^ (N + 1) * (c * c)) * U (N + 1) x)
          + (-((c ^ (N + 1) * c) * (((2 : Q') * x) * U (N + 1) x)))) := by
    -- First rewrite -(tailG (N+1)) into ( -(c^{N+2}u2) ) + (c^{N+3}u1)
    have hneg : (-(tailG c x (N + 1)))
        ≈ (-(c ^ (N + 2) * U (N + 2) x)) + (c ^ (N + 3) * U (N + 1) x) := by
      show (-((c ^ (N + 2) * U (N + 2) x) + (-(c ^ (N + 3) * U (N + 1) x))))
        ≈ (-(c ^ (N + 2) * U (N + 2) x)) + (c ^ (N + 3) * U (N + 1) x)
      refine eqv_trans _ _ _
        (neg_add_eqv (c ^ (N + 2) * U (N + 2) x) (-(c ^ (N + 3) * U (N + 1) x))) ?_
      exact add_eqv_congr_left _ _ _ (neg_neg_eqv (c ^ (N + 3) * U (N + 1) x))
    -- tailG N = (c^{N+1}u1) + (-(c^{N+2}u0))
    -- RHS = [ (c^{N+1}u1) + (-(c^{N+2}u0)) ] + [ (-(c^{N+2}u2)) + (c^{N+3}u1) ]
    have hsum : tailG c x N + (-(tailG c x (N + 1)))
        ≈ ((c ^ (N + 1) * U (N + 1) x) + (-(c ^ (N + 2) * U N x)))
          + ((-(c ^ (N + 2) * U (N + 2) x)) + (c ^ (N + 3) * U (N + 1) x)) := by
      refine add_eqv_congr_left _ _ _ hneg
    refine eqv_trans _ _ _ hsum ?_
    -- regroup the four terms: [A0 + (-D0)] + [(-D2) + B'] where
    --   A0 := c^{N+1}u1 (= A), D0 := c^{N+2}u0, D2 := c^{N+2}u2, B' := c^{N+3}u1 (= B).
    -- We want: A + (B + (-C)), with C = (p·c)·(2x·u1) and -(D0) + -(D2) = -C.
    -- Step 1: convert powers.  c^{N+2}·u0 ≈ (p·c)·u0, etc.
    -- Use cpow_n2 / cpow_n3.
    -- Rewrite D0 ≈ (p·c)·u0:
    have hD0 : c ^ (N + 2) * U N x ≈ (c ^ (N + 1) * c) * U N x :=
      mul_eqv_congr_right _ _ (U N x) (cpow_n2 c N)
    have hD2 : c ^ (N + 2) * U (N + 2) x ≈ (c ^ (N + 1) * c) * U (N + 2) x :=
      mul_eqv_congr_right _ _ (U (N + 2) x) (cpow_n2 c N)
    have hB' : c ^ (N + 3) * U (N + 1) x ≈ (c ^ (N + 1) * (c * c)) * U (N + 1) x :=
      mul_eqv_congr_right _ _ (U (N + 1) x) (cpow_n3 c N)
    -- Substitute:
    refine eqv_trans _ _ _
      (add_eqv_congr _ _ _ _
        (add_eqv_congr_left _ _ _ (neg_eqv_congr _ _ hD0))
        (add_eqv_congr _ _ _ _ (neg_eqv_congr _ _ hD2) hB')) ?_
    -- Now: [A + (-(pc·u0))] + [(-(pc·u2)) + B]
    -- Rearrange to A + (B + (-( (pc·u0) + (pc·u2) )))  then use recurrence.
    -- First: collapse (pc·u0)+(pc·u2) = pc·(u0+u2) = pc·(2x·u1) = C  (recurrence).
    -- We assemble the four terms into A + (B + (-(D0' + D2'))) with D0'=pc·u0, D2'=pc·u2.
    -- [A + (-D0')] + [(-D2') + B]
    --   ≈ A + ((-D0') + ((-D2') + B))         [add_assoc]
    --   ≈ A + ((-D0') + (B + (-D2')))         [add_comm inner]
    --   ≈ A + ((B + (-D2')) + (-D0'))? -> instead group negatives.
    -- Cleaner: A + (B + (-(D0' + D2'))).
    -- Path: [A + (-D0')] + [(-D2') + B]
    --   ≈ [A + (-D0')] + [B + (-D2')]                 [comm of inner pair]
    --   ≈ A + ((-D0') + (B + (-D2')))                 [add_assoc]
    --   ≈ A + (B + ((-D0') + (-D2')))                 [reorder: (-D0')+(B+(-D2')) ≈ B+((-D0')+(-D2'))]
    --   ≈ A + (B + (-(D0' + D2')))                    [neg_add]
    --   ≈ A + (B + (-C))                              [recurrence: D0'+D2' = C]
    have hcomm_inner : ((-((c ^ (N + 1) * c) * U (N + 2) x)) + (c ^ (N + 1) * (c * c)) * U (N + 1) x)
        ≈ ((c ^ (N + 1) * (c * c)) * U (N + 1) x + (-((c ^ (N + 1) * c) * U (N + 2) x))) :=
      add_comm_eqv _ _
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ hcomm_inner) ?_
    -- [A + (-D0')] + [B + (-D2')]  ≈  A + ((-D0') + (B + (-D2')))
    refine eqv_trans _ _ _
      (add_assoc_eqv (c ^ (N + 1) * U (N + 1) x) (-((c ^ (N + 1) * c) * U N x))
        ((c ^ (N + 1) * (c * c)) * U (N + 1) x + (-((c ^ (N + 1) * c) * U (N + 2) x)))) ?_
    refine add_eqv_congr_left _ _ _ ?_
    -- (-D0') + (B + (-D2'))  ≈  B + (-(D0' + D2'))
    -- (-D0') + (B + (-D2')) ≈ ((-D0') + B) + (-D2')   [assoc⁻¹]
    refine eqv_trans _ _ _
      (eqv_symm (add_assoc_eqv (-((c ^ (N + 1) * c) * U N x))
        ((c ^ (N + 1) * (c * c)) * U (N + 1) x) (-((c ^ (N + 1) * c) * U (N + 2) x)))) ?_
    -- ((-D0') + B) ≈ (B + (-D0'))
    refine eqv_trans _ _ _
      (add_eqv_congr_right _ _ _ (add_comm_eqv (-((c ^ (N + 1) * c) * U N x))
        ((c ^ (N + 1) * (c * c)) * U (N + 1) x))) ?_
    -- (B + (-D0')) + (-D2') ≈ B + ((-D0') + (-D2'))
    refine eqv_trans _ _ _
      (add_assoc_eqv ((c ^ (N + 1) * (c * c)) * U (N + 1) x)
        (-((c ^ (N + 1) * c) * U N x)) (-((c ^ (N + 1) * c) * U (N + 2) x))) ?_
    refine add_eqv_congr_left _ _ _ ?_
    -- (-D0') + (-D2') ≈ -(D0' + D2') ≈ -C
    refine eqv_trans _ _ _
      (eqv_symm (neg_add_eqv ((c ^ (N + 1) * c) * U N x) ((c ^ (N + 1) * c) * U (N + 2) x))) ?_
    refine neg_eqv_congr _ _ ?_
    -- D0' + D2' = (pc)·u0 + (pc)·u2 ≈ (pc)·(u0+u2) ≈ (pc)·(2x·u1) = C
    refine eqv_trans _ _ _
      (eqv_symm (mul_add_eqv (c ^ (N + 1) * c) (U N x) (U (N + 2) x))) ?_
    refine mul_eqv_congr_left (c ^ (N + 1) * c) _ _ ?_
    -- u0 + u2 ≈ 2x·u1   from  u2 = 2x·u1 + (-u0)
    -- U N x + U (N+2) x ≈ (2x)·U_{N+1} x
    show U N x + U (N + 2) x ≈ ((2 : Q') * x) * U (N + 1) x
    -- rewrite U (N+2) via recurrence
    have hrec : U (N + 2) x = ((2 : Q') * x) * U (N + 1) x + (-(U N x)) := U_succ_succ N x
    rw [hrec]
    -- U N x + ((2x)·u1 + (-(U N x))) ≈ (2x)·u1
    refine eqv_trans _ _ _
      (eqv_symm (add_assoc_eqv (U N x) (((2:Q')*x) * U (N + 1) x) (-(U N x)))) ?_
    -- (U N + (2x)u1) + (-(U N)) ≈ (2x)u1
    refine eqv_trans _ _ _
      (add_eqv_congr_right _ _ _ (add_comm_eqv (U N x) (((2:Q')*x) * U (N + 1) x))) ?_
    -- ((2x)u1 + U N) + (-(U N)) ≈ (2x)u1
    refine eqv_trans _ _ _
      (add_assoc_eqv (((2:Q')*x) * U (N + 1) x) (U N x) (-(U N x))) ?_
    refine eqv_trans _ _ _ (add_eqv_congr_left _ _ _ (add_neg_self_eqv (U N x))) ?_
    exact q_add_zero_eqv (((2:Q')*x) * U (N + 1) x)
  exact eqv_trans _ _ _ hL (eqv_symm hR)

/-! ## 4. The generating-function partial-sum telescoping identity (GF)

`factorC c x · Gpart c x (N+1) ≈ 1 − tailG c x N`, by induction on `N` using
`gf_step` (the per-step telescope) and the base `factorC·1 ≈ 1 − tailG c x 0`. -/

/-- The base case `factorC c x · Gpart c x 1 ≈ 1 + (−(tailG c x 0))`.
`Gpart c x 1 = 0 + c⁰·U₀ = 1`, `factorC·1 = factorC = 1 − 2cx + c²`, and
`1 − tailG 0 = 1 − (c·U₁ − c²·U₀) = 1 − (2cx − c²) = 1 + c² − 2cx`. -/
theorem gf_base (c x : Q') :
    factorC c x * Gpart c x 1 ≈ (1 : Q') + (-(tailG c x 0)) := by
  -- Gpart c x 1 = 0 + c^0·U_0 = 0 + 1·1.  factorC·(that) ≈ factorC.
  have hG : Gpart c x 1 ≈ (1 : Q') := by
    show (0 : Q') + (c ^ 0 * U 0 x) ≈ (1 : Q')
    refine eqv_trans _ _ _ (q_zero_add_eqv (c ^ 0 * U 0 x)) ?_
    show (1 : Q') * U 0 x ≈ (1 : Q')
    refine eqv_trans _ _ _ (one_mul_eqv (U 0 x)) ?_
    rw [U_zero]; exact eqv_refl _
  refine eqv_trans _ _ _ (mul_eqv_congr_left (factorC c x) _ _ hG) ?_
  refine eqv_trans _ _ _ (mul_one_eqv (factorC c x)) ?_
  -- factorC = (1+c²)+(-(2c·x)) ; target 1 + (-(tailG 0))
  -- tailG 0 = c^1·U_1 + (-(c^2·U_0)) = c·(2x) + (-(c·c·1))
  show (1 + c * c) + (-(((2:Q')*c)*x))
      ≈ (1 : Q') + (-((c ^ 1 * U 1 x) + (-(c ^ 2 * U 0 x))))
  -- RHS: rewrite U_1 = 2x, U_0 = 1, c^1 = c, c^2 = c·c
  rw [U_one, U_zero]
  -- 1 + (-( (c^1·(2x)) + (-(c^2·1)) ))
  -- normalise RHS inner: c^1·(2x) ≈ (2c)·x ; c^2·1 ≈ c·c
  have hc1 : c ^ 1 * ((2:Q') * x) ≈ ((2:Q')*c)*x := by
    show (c * c ^ 0) * ((2:Q') * x) ≈ ((2:Q')*c)*x
    -- c·c^0 ≈ c ; then c·(2x) ≈ (2c)·x
    refine eqv_trans _ _ _ (mul_eqv_congr_right _ _ ((2:Q')*x) (mul_one_eqv c)) ?_
    -- c·(2x) ≈ (2c)·x  : c·(2·x) ≈ (c·2)·x ≈ (2·c)·x
    refine eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv c (2:Q') x)) ?_
    exact mul_eqv_congr_right _ _ x (mul_comm_eqv c (2:Q'))
  have hc2 : c ^ 2 * (1 : Q') ≈ c * c := by
    show (c * (c * c ^ 0)) * (1 : Q') ≈ c * c
    refine eqv_trans _ _ _ (mul_one_eqv (c * (c * c ^ 0))) ?_
    refine mul_eqv_congr_left c _ _ (mul_one_eqv c)
  -- assemble RHS ≈ 1 + (-( (2c)x + (-(c·c)) ))
  refine eqv_symm ?_
  refine eqv_trans _ _ _
    (add_eqv_congr_left _ _ _ (neg_eqv_congr _ _
      (add_eqv_congr _ _ _ _ hc1 (neg_eqv_congr _ _ hc2)))) ?_
  -- 1 + (-( (2c)x + (-(c·c)) )) ≈ (1+c²) + (-(2c·x))
  -- push neg: -( a + (-b) ) ≈ (-a) + b
  refine eqv_trans _ _ _
    (add_eqv_congr_left _ _ _ (neg_add_eqv (((2:Q')*c)*x) (-(c*c)))) ?_
  refine eqv_trans _ _ _
    (add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _ (neg_neg_eqv (c*c)))) ?_
  -- 1 + ((-(2c·x)) + (c·c)) ≈ (1 + c·c) + (-(2c·x))
  refine eqv_trans _ _ _
    (eqv_symm (add_assoc_eqv (1:Q') (-(((2:Q')*c)*x)) (c*c))) ?_
  -- (1 + (-(2c·x))) + (c·c) ≈ (1 + c·c) + (-(2c·x))
  refine eqv_trans _ _ _
    (add_eqv_congr_right _ _ _ (add_comm_eqv (1:Q') (-(((2:Q')*c)*x)))) ?_
  -- ((-(2c·x)) + 1) + (c·c) ≈ (1 + c·c) + (-(2c·x))
  refine eqv_trans _ _ _ (add_assoc_eqv (-(((2:Q')*c)*x)) (1:Q') (c*c)) ?_
  exact add_comm_eqv (-(((2:Q')*c)*x)) ((1:Q') + c*c)

/-- **THE CHEBYSHEV-U GENERATING-FUNCTION PARTIAL-SUM IDENTITY (GF).**

For all `N`, `c`, `x`:
`factorC c x · (Σ_{n<N+1} cⁿ Uₙ(x)) ≈ 1 − (c^{N+1}·U_{N+1}(x) − c^{N+2}·U_N(x))`,
i.e. `factor(c,x)·Gpart(N+1) ≈ 1 + (−tailG N)`.

This is the finite, exact telescoping form of `1/(1−2cx+c²) = Σ cⁿ Uₙ(x)`.  Proved
by induction on `N`: the base is `gf_base`, the step adds the new summand and uses
the per-step telescope `gf_step` (`factorC·(c^{N+1}U_{N+1}) ≈ tailG N − tailG (N+1)`)
so the tails cancel. -/
theorem gf_telescope (c x : Q') :
    ∀ N, factorC c x * Gpart c x (N + 1) ≈ (1 : Q') + (-(tailG c x N))
  | 0 => gf_base c x
  | N + 1 => by
      -- factorC·Gpart(N+2) = factorC·(Gpart(N+1) + c^{N+1}·U_{N+1})
      --   = factorC·Gpart(N+1) + factorC·(c^{N+1}U_{N+1})
      --   ≈ (1 + (-tailG N)) + (tailG N + (-tailG (N+1)))   [ih, gf_step]
      --   ≈ 1 + (-tailG (N+1))                               [tailG N cancels]
      show factorC c x * (Gpart c x (N + 1) + (c ^ (N + 1) * U (N + 1) x))
        ≈ (1 : Q') + (-(tailG c x (N + 1)))
      refine eqv_trans _ _ _
        (mul_add_eqv (factorC c x) (Gpart c x (N + 1)) (c ^ (N + 1) * U (N + 1) x)) ?_
      refine eqv_trans _ _ _
        (add_eqv_congr _ _ _ _ (gf_telescope c x N) (gf_step c x N)) ?_
      -- (1 + (-tailG N)) + (tailG N + (-tailG (N+1))) ≈ 1 + (-tailG (N+1))
      -- regroup: 1 + ((-tailG N + tailG N) + (-tailG (N+1)))
      refine eqv_trans _ _ _
        (add_assoc_eqv (1:Q') (-(tailG c x N))
          (tailG c x N + (-(tailG c x (N + 1))))) ?_
      refine add_eqv_congr_left _ _ _ ?_
      -- (-tailG N) + (tailG N + (-tailG (N+1))) ≈ (-tailG (N+1))
      refine eqv_trans _ _ _
        (eqv_symm (add_assoc_eqv (-(tailG c x N)) (tailG c x N) (-(tailG c x (N + 1))))) ?_
      refine eqv_trans _ _ _
        (add_eqv_congr_right _ _ _ (neg_add_self_eqv (tailG c x N))) ?_
      exact q_zero_add_eqv (-(tailG c x (N + 1)))

/-! ## 5. The honest map of the deep target `κ = Σ_f r_f U_f`

`gf_telescope` is the per-Poisson-factor U-expansion tool.  We record precisely how
it feeds the existing reduced atoms, WITHOUT re-faking the deep analytic identity.

The proved-nonnegative node kernel `κ = ϑ₃·S` has:
  * `S = Σ_n sTerm`, `sTerm a x n = 2c/(1 + 2cx + c²)` with `c = a^{2n+1}`.  Since
    `1 + 2cx + c² = factorC (−c) x` (because `factorC (−c) x = 1 − 2(−c)x + (−c)² =
    1 + 2cx + c²`), `gf_telescope` gives the per-term U-expansion of each `sTerm`
    against `Σ_m (−c)^m U_m(x)` — the analytic content of "each `S`-term is a
    Chebyshev-U series".
  * `ϑ₃` a convergent product; its U-expansion is the multilinear product of the
    per-factor expansions (the `UsumFactorization` polynomial machinery is the
    finite shadow).

The full `κ = Σ_f rCoeff a f · U_f` is the differentiated Jacobi triple product
`ϑ₃·S = 2·Σ_n dTerm` — the genuinely-open analytic atom already NAMED in the
codebase as `JTPIdentity.DiffJTP` (we do NOT discharge or fake it).  The per-edge
truncation under the orthogonality integral is the strictly-smaller reduced atom
`ChebRProjection.RTruncTail a`, with `ChebRProjection.rProjection_of_tail` the
already-PROVED reduction to `MomentIntegralPSD.RProjection a`. -/

/-- `factorC (−c) x ≈ 1 + 2cx + c²` — the `sTerm` denominator `factor(c,x)` of
`HeatKernelPos` is `factorC` at the negated amplitude.  This is the precise hook
that makes `gf_telescope` the per-`S`-term Chebyshev-U expansion tool. -/
theorem factorC_neg (c x : Q') :
    factorC (-c) x ≈ (1 + c * c) + ((2 : Q') * c) * x := by
  -- factorC (-c) x = (1 + (-c)·(-c)) + (-( (2·(-c))·x ))
  show (1 + (-c) * (-c)) + (-(((2:Q') * (-c)) * x)) ≈ (1 + c * c) + ((2 : Q') * c) * x
  refine add_eqv_congr _ _ _ _ ?_ ?_
  · -- 1 + (-c)·(-c) ≈ 1 + c·c
    refine add_eqv_congr_left _ _ _ ?_
    -- (-c)·(-c) ≈ c·c
    refine eqv_trans _ _ _ (neg_mul_eqv c (-c)) ?_
    refine eqv_trans _ _ _ (neg_eqv_congr _ _ (mul_neg_eqv c c)) ?_
    exact neg_neg_eqv (c * c)
  · -- -((2·(-c))·x) ≈ (2·c)·x
    refine eqv_trans _ _ _
      (neg_eqv_congr (((2:Q') * (-c)) * x) ((-((2:Q')*c)) * x) ?_) ?_
    · -- (2·(-c))·x ≈ (-(2·c))·x
      refine mul_eqv_congr_right _ _ x ?_
      exact mul_neg_eqv (2:Q') c
    · -- -((-(2·c))·x) ≈ (2·c)·x
      refine eqv_trans _ _ _ (neg_eqv_congr _ _ (neg_mul_eqv ((2:Q')*c) x)) ?_
      exact neg_neg_eqv (((2:Q')*c) * x)

end YMGap.Continuum.ChebHeatKernelExpansion

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only via reused `Q'`/`Nat`/`Int` helpers).  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new `axiom`. -/

#print axioms YMGap.Continuum.ChebHeatKernelExpansion.factorC_eq_eval
#print axioms YMGap.Continuum.ChebHeatKernelExpansion.cpow_n2
#print axioms YMGap.Continuum.ChebHeatKernelExpansion.cpow_n3
#print axioms YMGap.Continuum.ChebHeatKernelExpansion.gf_step
#print axioms YMGap.Continuum.ChebHeatKernelExpansion.gf_base
#print axioms YMGap.Continuum.ChebHeatKernelExpansion.gf_telescope
#print axioms YMGap.Continuum.ChebHeatKernelExpansion.factorC_neg
