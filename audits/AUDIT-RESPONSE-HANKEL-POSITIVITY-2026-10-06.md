# Audit: Hankel / Hausdorff positivity of the response (2026-10-06 PT)

Module: `lean/YMGap/Continuum/BF4WilsonAllNomeResponseHankelPositivity.lean` (new leaf, additive).
Import: `YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen` (already built).

## 1. What is proved

On the completed all-nome carrier, for ANY vector `ψ`, the response is `R(n) = B(ψ, T^n ψ)`.
The coefficients are rational (`Q'`, the repo scalar). The plain sum is
`hankelSum [c_0,…,c_{N-1}] R m = Σ_{i<N} Σ_{k<N} c_i c_k R(i+k+m)`.

| Theorem | Statement (plain form) |
|---|---|
| `hankelSum_nonneg ψ cs m` | `Σ_i Σ_k c_i c_k R(i+k+m) ≥ 0`, every `m ≥ 0` |
| `hankelSum_nonneg_zero` / `_one` | the `m = 0` and `m = 1` cases |
| `hausdorffSum_first_nonneg ψ cs m` | `Σ_i Σ_k c_i c_k (R(i+k+m) − R(i+k+m+1)) ≥ 0` |
| `hausdorffSum_nonneg ψ cs m l` | `Σ_i Σ_k c_i c_k (∇^l R)(i+k+m) ≥ 0`, `∇R(n)=R(n)−R(n+1)` |
| `hankelForm_nonneg`, `hausdorffHankel_nonneg` | the same over arbitrary lag lists `[(c, lag)]` |

`(∇^l R)(n) = Σ_{r≤l} (−1)^r C(l,r) R(n+r) = (−1)^l Δ^l R(n)`.

Route: `v = Σ c_i T^i ψ` (`orbitSum`). `mixedMoment_nonnegative` gives
`B(v, T^m (I−T)^l v) ≥ 0`. The pin `inner_time_defectPower` gives
`B(x, T^n (I−T)^l y) = ∇^l(k ↦ B(x,T^k y))(n)`. `orbit_response_expand` gives
`B(v, T^n v) = Σ_i Σ_k c_i c_k R(i+k+n)`, and `∇^l` commutes with finite sums
(`hausdorffDiff_responseSum`, `hausdorffDiff_shift`).

- `m = 0` is `‖v‖²`.
- Odd `m` comes from positivity of `T` (`B(x,Tx) ≥ 0`) and self-adjointness.
- `l ≥ 1` uses `T ≤ 1`, which is already inside `mixedMoment_nonnegative`.
- There is no `T^{1/2}` and no spectral measure.

The shifted forms `m = 2p, 2p+1` are just instances of "every `m`".

## 2. Regressions

- `mixedMoment_eq_hausdorffDiff`: `mixedMoment ψ m l = (∇^l R)(m)`.
- `mixedMoment_nonnegative_via_hankel`: the existing lemma is the 1×1 case `cs = [1]`, via `hankelSum_singleton`.
- `hankelSum_pair` / `hankel2_nonneg`: the 2×2 case gives `a²R(m) + 2ab R(m+1) + b²R(m+2) ≥ 0`, with `2ab` written `a*b + a*b`.
- `hankel_logConvex_step`: `R(k+1)² ≤ R(k)R(k+2)` is re-exported from the existing Cauchy–Schwarz proof `response_log_convex_step` for the same `R`. It is NOT re-derived from the 2×2 Hankel form, because the constructive discriminant step was skipped.

## 3. Scope (honest)

- These are NECESSARY conditions only, and YM Numerics can test them on measured data.
- They hold for every vector on this carrier. They do not single out the YM anchor and give no survival, gap or continuum statement.
- Hausdorff's moment theorem, i.e. sufficiency or a representing measure on `[0,1]`, is NOT formalized.
- Only rational coefficients are covered. Real (RC) coefficients were not done.
- Log-convexity is not derived from the 2×2 form (see §2).

## 4. Build record

- Built on the box under the caps: `safe_lean_build.py --jobs 1`, `LEAN_NUM_THREADS=1`, `nice -n 10`, worker cap 3 GiB, reserve 1.5 GiB, process-group timeout 1800 s, 10 s sampler with abort below 1.5 GiB.
- One module was rebuilt; its upstream closure was already up to date. Compile time 4.9 s, wall time ~10 s.
- `#print axioms`: all 18 theorems give `[propext, Quot.sound]`.
- No warnings. `lean_forbidden_token_scan.py` reports `executable_forbidden_hits 0`.
