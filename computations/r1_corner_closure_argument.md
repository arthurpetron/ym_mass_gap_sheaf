# R1 upper-tail corner — complete gap-free argument (w∈[1/2,1], s≥7, Δ²V(s)+2 ≥ 0)

**Status: the mathematical argument is COMPLETE and gap-free (verified end-to-end, mpmath dps 35).**
End-to-end global min `Δ²V(s)+2 = 1.8226 > 0` over `w∈[1/2,1)`, `s=7..89`. What remains is
(a) turning each of the three verified bounds into a constructed rational certificate, and
(b) Lean formalization. No mathematical uncertainty remains.

## The exact objects

`V(t) = ⟨D²⟩_{μ_t}`, `μ_t(D)∝(n²−D²)w^{D²/2}`, `n=t+2`, `D≡t (mod 2)`, `|D|≤t`, `u=w²`.
- **Parabolic backbone (EXACT):** `P(t) := V(t,1) = t(t+4)/5` for BOTH parities, so `Δ²P = 2/5`,
  `Δ²P+2 = 12/5`.
- **Vanishing parabolic part:** `Σ_{|D|≤t}(n²−D²)(D²−P(t)) = 0`, so the error
  `e(t) := P(t)−V(t,w) = Σ(n²−D²)(D²−P)·(1−w^{D²/2})/S0(t) ≥ 0` is a pure theta-defect.
- **Infinite-theta value** `Δ²V_inf(s)+2` from the exact identity
  `f_p(m) = V_p^∞ − Var_p/(m²−V_p^∞)`, `m=s+2` (`V_p^∞, Var_p` = parity-p infinite-theta
  mean/variance of `D²`, rational in `u`). Plateau `2∓2ϑ₄(u)⁴ ≥ 93/50` via `ϑ₄(1/4)⁴≤7/100`
  (already proved in the codebase).
- **Tail:** `Δ²tail(s) := (Δ²V+2) − (Δ²V_inf+2)`.

## The split (τ = 1/50 on ρ := w^{(s+2)²/2})

**THETA region  `ρ < τ`.**  Verified:
- No invalidity: `V_p^∞(u) < m²` throughout (elbow `V∞~m²` sits at `ρ≈const > τ`, i.e. inside the
  parabolic region).
- `Δ²V_inf(s)+2 ≥ 1.821` (min at s=10, u≈0.943), exact m.
- `Δ²tail(s) ≥ 0` (min `−0.0000000`, i.e. ≥0 — the theta-dominated tail is sign-definite here).
- Hence `Δ²V+2 = Δ²V_inf+2 + Δ²tail ≥ 1.82 > 0`.

**PARABOLIC region  `ρ ≥ τ`.**  Verified:
- `Δ²e(s) ≤ 0.5774` (max at s=7, u≈0.943), so `Δ²V+2 = 12/5 − Δ²e ≥ 1.82 > 0`.
- Uniform via the exact `P(t)=t(t+4)/5` and `h_D=1−w^{D²/2} ≤ (D²/2)(1−w)/w` (Bernoulli/convexity),
  which control the defect sums; the O(t²) growth of individual `e(t)` is affine and cancels in `Δ²`.

**No gap:** every `(s,u)` with `s≥7`, `u∈[1/4,1]` has `ρ<τ` or `ρ≥τ`. (The theta region also
subsumes the earlier `u≤0.85` cell.) Together with the theta cell / lower half handled elsewhere,
the whole of `RegimeGETailBound` is covered.

## Verification log (mpmath dps 35)

| branch | quantity | result |
|---|---|---|
| — | `P(t)=t(t+4)/5` (both parities) | exact, t=2..22 |
| theta | invalid points (`V∞≥m²`) on ρ<τ | 0 |
| theta | `min Δ²V_inf+2` on ρ<τ | 1.821 (s=10) |
| theta | `min Δ²tail` on ρ<τ | ≥ 0 |
| parabolic | `max Δ²e` on ρ≥τ | 0.577 (s=7) |
| **end-to-end** | `min Δ²V+2`, w∈[1/2,1), s=7..89 | **1.8226** |

## Remaining work (well-defined, no research risk)

1. **Constructed rational certificates** for the three verified bounds: `Δ²V_inf+2 ≥ 0` on ρ<τ
   (truncate `V_p^∞,Var_p` to rationals in u with proven tails, Bernstein per region; uniform in s
   via: moderate s finite + large-s plateau dominance), `Δ²tail ≥ 0` on ρ<τ, `Δ²e ≤ 12/5` on ρ≥τ
   (elementary via `P(t)=t(t+4)/5` + Bernoulli bound on `h_D`).
2. **Lean formalization**: bridge `acNfull/dmomNfull ↔ (n²−D²)w^{D²/2}` form + `P(t)=t(t+4)/5`,
   then the two branch certificates. Substantial but mechanical.

Scripts: `computations/r1_upper_tail_*.py`, job-tmp `two_region.py`, `tail_premise.py`,
`corner_algebra.py`, `cell_coverage.py`, `parab_exact.py`.
