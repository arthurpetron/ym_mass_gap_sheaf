# Reconnaissance: the two box inequalities (the matched-retune crossover frontier) — 2026-06-21

The matched-retune quotient chain is wired end-to-end; its entire open content is two finite
`Q'` inequalities on the proved closed `(r,d)` box form `bondMovedCoeff_p2_rd` of the p=2
SU(2) heat-kernel self-fusion. This note records the numerical/structural reconnaissance done
BEFORE attempting their proof (the same discipline that caught the `renormW` retune bug and the
false folded 1-D product). Conclusion: unlike those, **both targets are TRUE, with comfortable
margin and explicit constants** — they are the genuine discrete local CLT, hard to prove but
correctly stated.

## Definitions (exactly as in Lean)

- `g_s = bondMovedCoeff N w 2 s` — the p=2 self-fusion coefficient (SU(2) Clebsch–Gordan).
- Matched retune `ρ`, `ρ³ = g₁/(2g₀)` (the EXACT s=1 ratio match; `MatchedRetuneP2`).
- Matched reference `ĉ_s = (s+1)·ρ^{C₄(s)}`, `C₄(s)=s(s+2)`; `ĉ_0=1`, `ĉ_1=2ρ³=g₁/g₀`.
- Step deviation `δ_k = (g_{k+1}·ĉ_k)/(g_k·ĉ_{k+1}) − 1`; `u = 1−w`, `y_s = u·C₄(s)`.
- Deflated sequence `h_s = g_s/ĉ_s` (so `δ_k = h_{k+1}/h_k − 1`).

## The two open obligations

- **`BoxRatioDominance`**: `g_{k+1}·ĉ_k ≥ g_k·ĉ_{k+1}` for `k≥1`, i.e. `δ_k ≥ 0`, i.e. `h_s`
  non-decreasing ("self-fusion has heavier tails than the matched kernel").
- **`BoxRatioDerivative`**: `δ_k ≤ C·u³·(2k+3)` (note `y_{k+1}−y_k = u·(2k+3)`), telescoping to
  `∑_{k<s} δ_k ≤ C·u²·y_s`.

## Findings (numerics; `w=e^{−τ}`, τ from 0.2 to 0.006; exact `ρ`)

| τ | DOM δ_k≥0 (k≥1) | C = sup δ_k/(u³(2k+3)) | active-window ∑δ_k | ρ/w^{1/2} | h_∞/h_1 |
|---|---|---|---|---|---|
| 0.20 | 9+/0− ✓ | 0.356 | 0.156 | 0.9982 | 1.077 |
| 0.10 | 14+/0− ✓ | 0.316 | 0.040 | 0.9982 | — |
| 0.05 | 20+/0− ✓ | 0.281 | 0.009 | — | — |
| 0.025 | 29+/0− ✓ | 0.270 | 0.002 | 0.9999 | 1.005 |
| 0.0125 | 42+/0− ✓ | 0.269 | 0.0005 | — | — |
| 0.00625 | 61+/0− ✓ | 0.274 | 0.0001 | 0.99999 | 1.0003 |

1. **Dominance holds strictly** — every `δ_k>0` (`minCk>0`, no near-misses) at every τ. `h_s` is
   strictly increasing.
2. **Derivative constant** `C → ≈0.27`, bounded and uniform in τ ⇒ the bound holds with a safe
   **`C = 1/2`** (or even the observed `≈0.36` ceiling).
3. **Engine smallness** (the `B≤1/2` side-condition): active-window `∑δ_k ≤ 0.156` (worst case,
   largest τ) and `→0` — comfortably satisfied; worst case is the LARGEST τ in the band.
4. **`h_s` non-decreasing to a bounded plateau**, `h_∞/h_1 → 1` (`1.077→1.005→1.0003`): the
   deflated self-fusion is nearly flat — the matched retune is genuinely the right reference;
   the total log-increment `∑δ_k = log(h_∞/h_1) → 0`.
5. **`ρ/w^{1/2} = 1 + O(τ²)`** (`0.9982→0.99999`): the EXACT cube-root match and the clean
   `w^{1/2}` differ exactly at the quadratic order being bounded ⇒ the exact `ρ³=g₁/2g₀` match is
   NECESSARY (substituting `w^{1/2}` would inject an `O(τ²)` error of the same size as the
   residual). The constructive cube root was not optional.

## Implications for the proof

- The targets are correct (not false like `renormW`/folded-product). The proof is the genuine
  local CLT on the box form; the constants (`C=1/2`, smallness) are explicit.
- Cleanest framing: prove `h_s=g_s/ĉ_s` is non-decreasing (DOMINANCE) and its multiplicative
  increments satisfy `h_{k+1}/h_k − 1 ≤ C·u³·(2k+3)` (DERIVATIVE). The deflated sequence being
  near-flat (plateau `→1`) is why a fixed polynomial `P=C(1+y)` envelope works.
- The `δ`-mass concentrates at moderate `y≈O(10)` (active-window edge), so an active-window
  pointwise bound + a tail argument (heat-kernel decay past the moving cutoff) is the natural
  decomposition — consistent with the engine's active-window `B≤1/2` requirement.
- Likely proof levers (per the deep-research toolkit): the `(r,d)` box increment `g_{k+1}−g_k`
  exposing the `(2k+3)` factor; `secondOrder_qpow` for the `u²` gain on the `ρ`-power mismatch;
  PF₂/log-concavity (`coeffW_ratio_mono`) as the dominance guardrail; sharp two-sided S³
  heat-kernel bounds (Nowak–Sjögren–Szarek) / Bessel-ratio bounds if a sharper handle on
  `g_{k+1}/g_k` is needed.

## Honest status

This is reconnaissance, not proof: it establishes that `BoxRatioDominance` and
`BoxRatioDerivative` are TRUE with margin and explicit constants, so the matched-retune chain's
sole remaining analytic content is a correctly-stated (hard) discrete local CLT — NOT a false
target, NOT a 4D Yang–Mills mass gap.

## ADDENDUM (2026-06-21) — the bracketed targets are FALSE-as-stated; fix fork

Before launching proofs, a second reconnaissance on the EXACT Lean structures
(`BoxRatioDominance`/`BoxRatioDerivative`, which use `coeffMatchedLo/Hi`) found they are
FALSE as currently defined. `coeffMatchedHi/Lo R s = (s+1)·qpow (rhoHi/rhoLo) (c4 s)` — the
NAIVE bracket — raises the loose rational `ρ`-bracket to `C₄(s) ≈ s²`, so the bracket ratio
`(rhoHi/rhoLo)^{C₄(s)}` EXPLODES. With `rhoLo/rhoHi` taken at the FIXED bisection stage 1
(width ≈ ½), the bracketed inequalities fail immediately (even `k=1`).

NUMERICS (decomposed brackets `R^{⌊C₄/3⌋}·ρ^{C₄%3}`, `R=ρ³=g₁/2g₀` exact, only the residual
`ρ^{C₄%3}∈{1,ρ,ρ²}` bracketed ⇒ slack `≤(rhoHi/rhoLo)²` bounded; vs bisection depth):
- DERIVATIVE (C=½): becomes TRUE at depth `~const·log(1/u)` (d12 at τ=.1, d16 at τ=.025,
  d24 at τ=.0062) — the explicit `Cu³(2k+3)` slack absorbs the bounded bracket error. Q'-fixable.
- DOMINANCE (sign, `δ_k≥0`): margin `δ_1 ~ τ³ → 0`, so NO fixed depth works uniformly as
  `w→1`; even decomposed brackets fail at τ≤.025 up to depth 24. Needs the EXACT `ρ` (CReal),
  where `δ_k>0` holds with no bracket slack.

CONSEQUENCE: `coeffMatchedLo/Hi` (naive) must be replaced by DECOMPOSED brackets, and
`rhoLo/rhoHi` by a `w`-dependent (growing) bisection depth. The DERIVATIVE then closes in Q';
the DOMINANCE needs the exact-`ρ` CReal reference (vanishing margin). The EXACT inequalities
remain TRUE with margin (the main recon above) — only the bracketed Q' surrogates were broken.

FIX FORK: (A) Q' decomposed brackets + `w`-growing depth — works for derivative, awkward for
the vanishing-margin dominance; (B) restate both against exact `CReal` `ĉ_s=(s+1)ρ^{C₄(s)}`
(no slack; uses the new `CRealAlg`/`CRealContinuumAlg` layer) — cleaner for dominance, needs
CReal inequality machinery. Likely: (A) for derivative, (B) for dominance.
