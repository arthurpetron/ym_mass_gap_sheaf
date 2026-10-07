# P10: scope of a nested two-level multilevel scheme for side 4 (estimate only; not implemented) — 2026-10-06

## Why side 4 is hard
For s=4, W = R_Y(5)/R_Y(2).

**Pilot values** (d=4, nsub=40, 534 cfg):
- Denominator: R_Y(2)/R_Y(0) = 0.029(7).
- Numerator: R_Y(5)/R_Y(0) = 0.000(8).
- Result: W = 0.02(27).

**Where the error comes from.**
- The numerator error alone contributes 0.008/0.029 ≈ 0.27.
- So ±0.03 needs about 9x less error on R_Y(5), i.e. about 80x less variance.
- R_Y(5) is a box sum of R(5..13), with weights peaking at n=9.
- R_Y(2) is a box sum of R(2..10), and its relative error (24%) comes mostly from lags 2–4. The one-level scheme gives those lags only a 1–2x gain.

**One-level d=4, nsub=40, extrapolated from the pilot:**
- ±0.03 at s=4 needs ≈ 4e4 configs.
- That is ≈ 48 h on 2 threads, or ≈ 25–30 h on 4 threads.
- P10 will measure the nsub=100 gain at s=4 directly. If the gain keeps growing, this drops.

## Nested scheme (Lüscher–Weisz 2-level)
**Levels.**
- Outer level: freeze spatial links on t % 8 == 0.
- For each of n_out outer updates (1 sweep of all non-frozen links), freeze t % 4 == 0 as well and run n_in inner updates.

**What to accumulate:**
- (i) Inner one- and two-point averages S1_in[t] and S2_in[t,u], with t and u in the same 4-slab.
- (ii) Per outer update, the products S1_in[t]·S1_in[u] for t and u in different 4-slabs of the same 8-slab. Average these over the outer updates into P8[t,u].
- (iii) The outer one-point average S1_out[t] = mean over outer updates of S1_in[t].

**Correlator:**
- C(t,u) = S1_out[t]·S1_out[u] when t and u are in different 8-slabs.
- C(t,u) = P8[t,u] when they are in the same 8-slab but different 4-slabs.
- C(t,u) = S2 when they are in the same 4-slab.
- Interior-pairs estimator and matched-mean subtraction as in P9/P10.

**Code change** (src/main.rs, about 80–120 lines):
- A second class list that excludes mu ≥ 1 at t % 8 == 0.
- A nested loop over outer and inner updates.
- The three accumulators.
- A new record layout: Lt + Lt·Lt (S1_out, P8) + Lt·Lt (S2), plus timings.
- About 40 lines of analysis on top of `ana/p10_report.py`.
- Test on 8^3x16 against the direct chain, as in P9.
- **Effort:** about 2–3 h coding and testing, plus a 1-h pilot at 16^3x32 to measure the gain.

**Cost per config:**
- n_out·(outer sweep + n_in inner sweeps) at about 0.05 s per sub-sweep on 4 threads.
- Example: n_out=10, n_in=20 gives ≈ 210 sub-sweeps ≈ 11 s/config, about 2x the P10 cost.

## Expected gain and wall time for ±0.03 at side 4
- **Pairs 8 or more apart** (different 8-slabs): the gain roughly multiplies. One-level d=4 already gives 11–13x at n=8–13; nesting could plausibly add another 3–10x for these lags.
- **Lags 4–7** keep roughly the one-level gain.
- **Lags 2–3** (which set the denominator) gain nothing extra.
- With R_Y(5)'s weights spread over n=5..13 (about half at n ≥ 8), the variance of the s=4 numerator should drop about 2–4x at equal cost versus one-level d=4. The denominator error (24%) is unchanged and would need more configs anyway.
- **Estimate:** ±0.03 at s=4 in ≈ 8–15 h wall on 4 threads with the nested scheme, versus ≈ 25–30 h one-level. Both figures are uncertain by about 2x until piloted.
- **Caveat:** since R_Y(2) ≈ 0.03·R_Y(0), W(s=4) stays a ratio of small numbers. A ±0.03 error on W means resolving R_Y(5) to about 1e-3·R_Y(0).

## Recommendation
- First read P10's nsub=100 gain at s=4. If it is ≥ 2x the nsub=40 gain, a longer one-level run (about 12–15 h) may be simpler than the nested code.
- Otherwise implement the nested scheme and pilot it for 1 h before committing to a long run.
