# Gauss's q-binomial identity over `Q'` — notes

Companion to `lean/YMGap/Continuum/GaussQBinom.lean` (namespace
`YMGap.Continuum.GaussQBinom`).  This is the **Wall-2 finite engine**: the
Gaussian-theta-weight analogue of the geometric-weight telescoping engine
(`UTelescope.uTelescope_all`).

## 1. Why this module exists

The continuum-positivity heat-kernel identity needs the *Gaussian* weight
`a^{n²}` of the Jacobi theta function `ϑ₃` (the "differentiated Jacobi triple
product" `K_t = (ϑ₃/2a)·S`).  The existing Chebyshev-`U` telescoping engine
handles only a *geometric* `zⁿ`-weighted series

```
(1 − 2xz + z²)·Σ_{n=0}^{M} U_n(x) zⁿ  ≈  1 − U_{M+1} z^{M+1} + U_M z^{M+2}
```

and cannot reach `q^{n²}`.  The missing finite combinatorial heart is **Gauss's
q-binomial identity**, which produces exactly the `q^{k²}` Gaussian
coefficients:

```
∏_{j=1}^{N} (1 + z·q^{2j−1})  =  Σ_{k=0}^{N} q^{k²} · ⟨N,k⟩_{q²} · z^k,        (★)
```

where `⟨N,k⟩_Q` is the Gaussian binomial (q-binomial) with base `Q = q²`.  This
module formalizes (★) over the project's constructive rationals `Q'`, for **all
N**, by induction on `N` driven by the q-Pascal recurrence.

## 2. The statement proved

```lean
theorem gauss_qbinom_all (z q : Q') : ∀ N, qProd z q N ≈ gaussSum z q N
```

where `≈` is `Q'.eqv` (semantic rational equality on the unnormalized `Q'`),
`qProd z q N = ∏_{j=1}^{N}(1 + z·q^{2j−1})`, and
`gaussSum z q N = Σ_{k=0}^{N} q^{k²}·⟨N,k⟩_{q²}·z^k`.  `z, q` are *general*
`Q'` parameters (the application puts `z = e^{iθ}`, `q = a`, but (★) is purely
algebraic — exactly as `uTelescope_all` is general in `x, z`).

The identity is **CLOSED for all N**.  No `sorry`, no residual gap.

## 3. Definition choices

`Q'` has no division (AGENTS.md Rule 3 forbids Mathlib `ℝ`; `Q'` is the
unnormalized exact-rational substrate), so the q-binomial is defined
**recursively via q-Pascal**, never via a q-factorial quotient.  Structural
recursion on both `N` and `k` keeps `Nat` truncated subtraction out of the
*definition*:

```
qbin Q 0     0     = 1
qbin Q 0     (k+1) = 0
qbin Q (N+1) 0     = 1
qbin Q (N+1) (k+1) = qbin Q N (k+1) + Q^(N−k) · qbin Q N k
```

This is exactly the Gaussian-binomial recursion
`⟨N+1,k⟩ = ⟨N,k⟩ + Q^{(N+1)−k}·⟨N,k−1⟩` (here `(N+1)−(k+1) = N−k` and
`(k+1)−1 = k`, both structural).  q-Pascal `qbin_succ_succ` is therefore
definitional (`rfl`).  Out-of-range entries are `0` (`qbin_out_of_range`,
proved `≈ 0` by induction since `Q'.mul`/`Q'.add` by `0` is only *semantically*
zero on the unnormalized `Q'`).

Numerically verified (kernel `#eval`): `⟨3,1⟩₂ = 7 = 1+2+4`,
`⟨4,2⟩₂ = 35 = (2⁴−1)(2³−1)/((2²−1)(2−1))`, and the full identity (★) holds at
`(z,q) = (3,2)` for `N = 3,5` and at `(z,q) = (1/3, 1/2)` for `N = 4`.

The product side `qProd` and the running sum `gaussSumUpto` are recursive
`def`s mirroring how `uSeries`/`telescopeRHS` build their products/sums in
`UTelescope.lean`.

## 4. Method — `eqv`-`calc` over the hand-built `Q'` ring layer

No `ring`/`linarith`/Mathlib for `Q'` identities (Rule 3): they hold only up to
`Q'.eqv`, and the two sides generally carry *different* denominators.
Everything routes through the proven `Q'.eqv` ring lemmas (`Cheb.add_mul_eqv`,
`mul_add_eqv`, `mul_eqv_congr`, `add_eqv_congr`, the congruences,
`add_assoc_eqv`/`add_comm_eqv`, …), keeping powers as opaque atoms via
`Q'.pow_succ` (a `rfl`).  (Pure `Nat`-exponent arithmetic — e.g.
`(k+1)² + 2(N−k) = (2N+1) + k²` — is discharged by `omega` after a manual
`Nat`-square expansion, since `omega` is linear and treats `k*k`, `(k+1)*(k+1)`
as opaque atoms.)

### The induction

The product recursion `qProd (N+1) = qProd N · (1 + z·q^{2N+1})` and the IH
`qProd N ≈ gaussSum N` reduce the step (`gauss_qbinom_step`) to the pure
finite-sum identity (no product left):

```
gaussSum z q N · (1 + z·q^{2N+1})  ≈  gaussSum z q (N+1)        (gaussSum_step)
```

This is the entire algebraic content.  It is assembled from two pieces:

1. **`shift_term_eqv`** — the exponent bookkeeping
   `(z·q^{2N+1})·gaussTerm N k ≈ q^{(k+1)²}·(Q^{N−k}·⟨N,k⟩)·z^{k+1}` for
   `k ≤ N`, i.e. `k² + (2N+1) = (k+1)² + 2(N−k)` and `Q = q·q ⟹ Q^{N−k} =
   q^{2(N−k)}`.  This is *why* the `q^{k²}` Gaussian weight is exactly what the
   product generates.
2. **`gaussTerm_pascal`** — the q-Pascal split lifted to weighted terms:
   `gaussTerm (N+1) (k+1) ≈ gaussTerm N (k+1) + (z·q^{2N+1})·gaussTerm N k`.

A running induction on the summation bound `M ≤ N` (`gaussSum_run`) carries the
pending "shift" of the last term; at the full bound `M = N` it closes because
the missing top term `gaussTerm (N+1) (N+1)` is supplied precisely by the shift
of the index-`N` term (its q-Pascal second branch; the first branch
`gaussTerm N (N+1) = 0` since `⟨N,N+1⟩ ≈ 0`).

## 5. Axiom gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only via the reused `Int`/`omega` helpers in the `Q'` base
layer; `qbin_succ_succ` depends on **no** axioms).  No `Classical.*`, no
`sorry`/`sorryAx`, no `native_decide`.  `#print axioms` footers are present for
all nine load-bearing declarations and verified in the build log:

```
qbin_succ_succ      — (no axioms)
qbin_out_of_range   — [propext, Quot.sound]
pow_add_eqv         — [propext]
shift_term_eqv      — [propext, Quot.sound]
gaussTerm_pascal    — [propext, Quot.sound]
gaussSum_run        — [propext, Quot.sound]
gaussSum_step       — [propext, Quot.sound]
gauss_qbinom_base   — [propext]
gauss_qbinom_step   — [propext, Quot.sound]
gauss_qbinom_all    — [propext, Quot.sound]
```

## 6. Where this plugs in

`gauss_qbinom_all` is the Gaussian-weight finite engine.  Specialising
`z = e^{iθ}`, `q = a` (the heat-kernel amplitudes) and taking `N → ∞`, the
product `∏(1 + a^{2j−1} z)` is one of the two `z`-factors of the Jacobi triple
product for `ϑ₃`, and the right side is its `q^{k²}`-Gaussian expansion — the
theta weight the geometric `UTelescope` engine could not reach.  As with
`UTelescope`'s `truncation_identity`, the residual is the single `N → ∞`
convergence input; the finite combinatorial algebra is now fully discharged.

## 7. Remaining gap

**None at the finite-algebra level.**  The full general-`N` Gauss identity (★)
is closed.  The only thing *not* in this module is the analytic `N → ∞` limit
(convergence of the truncated theta product), which is the standing G1-type
convergence input shared with `HeatKernelConv`/`ThetaConv`/`UTelescope` and is
out of scope for the finite engine.
