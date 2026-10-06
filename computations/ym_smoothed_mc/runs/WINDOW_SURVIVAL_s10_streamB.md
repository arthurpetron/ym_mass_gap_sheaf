# beta = 3.0, 32^3x48, side 10: stream B and the A/B comparison (2026-10-06 05:30 PT)

Stream B (seed 3002, 170 measurements, interval 4, therm 300) finished 04:38 PT.
Analysis: `ana/window_table.py`, `ana/p5_interim.py`, same binning/jackknife as stream A.

| stream | rho | W = R(s+1)/R(s/2) | eps*side |
|---|---|---|---|
| A (seed 3001) | 0.75 | 0.23(12) | 2.89(12) |
| A (seed 3001) | 1.00 | 0.23(12) | 2.28(13) |
| B (seed 3002) | 0.75 | 0.26(18) | 2.49(12) |
| B (seed 3002) | 1.00 | 0.26(17) | 1.898(87) |
| A,B each vacuum-subtracted, then averaged | 1.00 | 0.26 (no error bar yet) | 2.05 |
| A+B naively pooled (ONE mean subtracted) | 1.00 | 0.48(11) | 1.82(11) |

## Caveats (important for anything that cites the side-10 point)

1. The two streams disagree. At rho = 1, eps*side is 2.28(13) vs 1.898(87), about 2.4 sigma apart.
   So "the plateau holds at side 10" is NOT established. The side-10 value is somewhere
   around 1.9-2.3 and may be slightly below side 6/8 (2.37, 2.36).
2. The timeslice-averaged operator mean differs between streams:
   <M> = 0.8745(23) for A vs 0.8546(41) for B, about 4 sigma. Stream B's two halves are 0.8435 and 0.8657.
   The operator mean has a long autocorrelation (binning tau_int for M is still growing:
   0.5, 0.93, 1.65, 3.08, 5.71 at bins 1-16 in the pooled set). So the quoted error bars are
   underestimates at side 10.
3. Pooling the streams with one global mean adds the between-stream variance as a constant
   to C(n). That inflates the large-lag correlator: W goes 0.26 -> 0.48, and R(4u)/R(2u) -> 0.97.
   The window ratio W at large side is therefore sensitive to slow modes and to vacuum subtraction,
   because R(s+1) is ~8% of R(0) here. Any claim that "W does not drift to 0" at side >= 10 must
   use per-stream (or per-block) subtraction or a subtraction-free estimator, plus more streams.
4. Physical spatial box is small (Ls*a/sqrt(t0) ~ 5.0 at beta = 3.0), so finite-volume states
   (torelons) and slow sectors are plausible contaminants of the large-lag survival.

Follow-up launched 05:29 PT on the box: stream C (seed 3003, therm 400, otherwise identical),
ETA about 07:55 PT. All of this is numerics on the smeared loop with the Wilson action,
not the Lean anchor state, and proves nothing.
