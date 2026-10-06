# Audit: window survival vs. a gap contraction, a NECESSARY compatibility condition (2026-10-06 UTC)

File: `lean/YMGap/Continuum/BF4WilsonAllNomeWindowGapCompatibility.lean` (new leaf;
imports only `BF4WilsonAllNomeShiftedWindowSurvival`). Constructive, Mathlib-free,
no sorry/admit/Classical/native_decide. Every theorem prints axioms
`[propext, Quot.sound]`.

## What it says, honestly

This is a NECESSARY compatibility condition between two branches:
- the nontriviality branch: the anchor survives the backward window,
  `PathShiftedWindowSurvival`;
- the gap branch: a contraction `r_j < 1` on the anchor's orbit.

Both can hold at scale `j` only if `side_j (1 - r_j) ≤ C(θ) = 2(1-θ)/θ`. In words,
`side_j` must be at most of the order of the correlation length in lattice units,
`1/(1-r_j)`.

It proves NEITHER branch:
- window survival stays OPEN;
- no `r_j < 1` is constructed;
- nothing about a mass gap or nontriviality follows.

## Statements (as proved)

`R(n) = B(x, T^n x)`; `OrbitContraction x r :≡ ∀ k, B(T^(k+1)x, T^(k+1)x) ≤ (r*r)·B(T^k x, T^k x)`.

Moment-only core, for any `R : Nat → RC`:
- `even_contraction_iterate`:
  - hypothesis: `∀ k, R(2k+2) ≤ (r*r) R(2k)`;
  - conclusion: `R(2(m+q)) ≤ (r*r)^q R(2m)`.
- `window_contraction_compat`:
  - hypotheses: `0 < fl`, `2*((p+1)/2) + 2*q ≤ s+1`, `R` antitone, the even
    contraction, `Rq fl ≤ R(p)`, and `θ·R(p) ≤ R(s+1)`;
  - conclusion: `θ ≤ (r*r)^q`.
- `window_contraction_compat_floor`: same hypotheses with `p ≤ s+1` in place of the
  constraint on `q`; conclusion `θ ≤ (r*r)^((s+1)/2 - (p+1)/2)`.

Scalar part (rational):
- `bernoulli_cleared`: for `0 ≤ r ≤ 1`, `r^n · (1 + n(1-r)) ≤ 1`.
- `rate_of_contraction_power`: for `0 ≤ r ≤ 1` and `θ ≤ (r*r)^q`,
  `θ · (2q·(1-r)) ≤ 1 - θ`.
- `side_rate_of_contraction_power`: with `L = 2·(2q)`, `θ · (L(1-r)) ≤ (1-θ)·2`.
- `side_rate_le_c0`: if also `0 < θ` and `(1-θ)·2 ≤ θ·c0`, then `L(1-r) ≤ c0`.

Completed carrier, generic over `x : V`:
- `orbit_even_contraction`: `OrbitContraction x r` gives `R(2k+2) ≤ (r*r) R(2k)`, via
  `shift_norm_pin`.
- `window_gap_compat`:
  - hypotheses: `0 < fl`, `p ≤ s+1`, `OrbitContraction x r`, `Rq fl ≤ R(p)`, and
    `θ R(p) ≤ R(s+1)`;
  - conclusion: `θ ≤ (r*r)^((s+1)/2 - (p+1)/2)`.
  - Antitonicity comes from `response_le_of_le`, which is unconditional on this
    carrier.

Path form, `PathOrbitContraction tr r :≡ ∀ j, OrbitContraction (state j) (r j)`. All
three theorems are for `j ≥ 2`:
- `path_windowSurvival_contraction_exponent`:
  - hypotheses: `PathShiftedWindowSurvival tr θ`, `PathShiftedNondegenerate tr fl`
    (`0 < fl j`) and `PathOrbitContraction tr r`;
  - conclusion: `θ ≤ (r_j*r_j)^(side_j/4)`, i.e. `θ ≤ r_j^(side_j/2)`.
- `path_windowSurvival_forces_rate`: adding `0 ≤ r_j ≤ 1` gives
  `θ · (side_j · (1 - r_j)) ≤ (1-θ)·2`.
- `path_windowSurvival_forces_rate_c0`: adding `0 < θ` and `(1-θ)·2 ≤ θ·c0` gives
  `side_j (1-r_j) ≤ c0`.

Index bookkeeping:
- The nondegeneracy floor at `side_j` passes down to `side_j/2` by antitonicity, so
  `R(p) > 0` at the index the division needs.
- The window has `p = side_j/2` and `s+1 = side_j+1`.
- With `side_j = 2^j` and `j ≥ 2`,
  `q = ⌊(side_j+1)/2⌋ - ⌈side_j/4⌉ = side_j/4 = ⌊(side_j+1-p)/2⌋`.

## Correction to the requested exponent

The request was `θ ≤ r^(2⌊(s+1-p)/2⌋)` with the parity step done by
monotonicity. What monotonicity actually delivers is
`q = ⌊(s+1)/2⌋ - ⌈p/2⌉`, because even lags are orbit norms and odd lags are not:
- `p` even: `q = ⌊(s+1-p)/2⌋`, as requested.
- `p` odd and `s+1-p` odd: `q = ⌊(s+1-p)/2⌋`, as requested.
- `p` odd and `s+1-p` even: `q = ⌊(s+1-p)/2⌋ - 1`. One factor `r²` is lost, because
  `R(2m+1)` is only bounded below by `R(2m+2)`.

The requested exponent is still TRUE in that last case, by a paper argument:
- Log-convexity `R(n+1)² ≤ R(n)R(n+2)` (`response_log_convex_step`) gives
  `R(n+1)R(n+2) ≤ R(n)R(n+3)`.
- Combined with the contraction at `k+1`, this gives `R(2k+3) ≤ r² R(2k+1)`.
- Both steps cancel a positive factor, which is not formalized here.

The path form is unaffected: `p = side_j/2` is even for `j ≥ 2`. The case `j = 1`
(`side = 2`, `p = 1`) is omitted, since the proved exponent there is 0.

## C(θ)

`C(θ) = 2(1-θ)/θ`, used in the cleared form `(1-θ)·2 ≤ θ·c0`.
- It is the same constant that turns window survival into the shifted H1
  (`pathShiftedEpsBound_of_windowSurvival`).
- Derivation: `θ ≤ r^(side/2)` together with Bernoulli `r^n ≤ 1/(1+n(1-r))` gives
  `θ(1 + (side/2)(1-r)) ≤ 1`.

## Remark (paper, not formalized)

The norm-form `OrbitContraction x r` follows from the existing vacuum Rayleigh rate
`WilsonVacuumRayleighRate r` (`B(y,Ty) ≤ r B(y,y)` on the vacuum complement):
- Use the one-step Cauchy–Schwarz `R(2k+2)² ≤ R(2k+1)R(2k+3)`.
- Apply the Rayleigh rate at `T^k x` and at `T^(k+1) x`.
- Cancel the positive factor `R(2k+2)`.

So this result and `path_shiftedEps_forces_rate` express the same screen.

## Resources (Mac, single-file check only)

- Pre-run: one Lean-ish process (CleanShot X only).
  - `memory_pressure` free 46–47%, load1 8.8–10.0, swap 0.92/2 GiB, avail ≈ 15.4 GiB.
  - Import closure verified up to date with `--no-build` (3284 jobs); no olean
    rebuild.
- Check: `nice -n 10`, `safe_lean_build.py --jobs 1 --check-worker-limit-gib 8`
  (the launcher sets LEAN_NUM_THREADS = jobs = 1), process-group-kill monitor with a
  10 s sampler.
  - Exit 0, 11 s, no warnings.
  - Peak load1 11.34; min avail 15035 MiB; free 46%; swap 920.75 MiB, unchanged.
- Caveat: the kernel pressure level (`kern.memorystatus_vm_pressure_level`) read 2
  (warning) before and after the 11 s run, even though `memory_pressure` reported
  46% free.
  - The pre-run gate only checked the free percentage.
  - The run ended before the first in-loop sample, which would have aborted it.
  - The helper now refuses to start at level ≥ 2.

## Held

The anchor-swap restatement (pending YM Numerics W on the exact Y_j), F1–F4, G1–G8
and FV1–FV4 are unchanged.
