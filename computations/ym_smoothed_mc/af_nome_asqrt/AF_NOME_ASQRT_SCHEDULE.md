# afNomeSchedule a√σ literature check (j = 4…8)

**MC / published lattice data only — not a proof** of RG summability, asymptotic freedom, or any Lean theorem.
Date: 2026-10-06. Repo: `computations/ym_smoothed_mc/af_nome_asqrt/`.
Repro: `python3 af_nome_asqrt_schedule.py`.

## Schedule

From `BF4WilsonAllNomeAFPaddedTrajectory.lean` / `P11_TRAJECTORY_PLAN.md`
(A recalibrated to `1942/1000`):

\[
1 - w_j = \frac{A}{j + \kappa\lfloor\log_2(j+1)\rfloor + C},
\qquad A = 1.942,\; \kappa = 51/121,\; C = 4.
\]

\[
\beta_j = -\frac{1}{2\ln w_j}
\quad\bigl(= 4/g^2 \text{ with } g^2 = -8\ln w\bigr).
\]

### Computed \((j, w_j, \beta_j)\)

| j | \(w_j\) | \(\beta_j\) |
|---|--------:|----------:|
| 4 | 0.780391 | 2.016449 |
| 5 | 0.802702 | 2.275087 |
| 6 | 0.820898 | 2.533485 |
| 7 | 0.841656 | 2.900510 |
| 8 | 0.853594 | 3.158562 |

(Matches the plan’s rounded table 2.02 / 2.28 / 2.53 / 2.90 / 3.16.)

## Literature \(a\sqrt{\sigma}\) table

Primary knots: Fingberg–Heller–Karsch (FHK) compilation, Nucl. Phys. B 392 (1993) 493
[hep-lat/9208012] Table 3 (SU(2) Wilson, large lattices). β = 2.85 also UKQCD /
Booth et al., Nucl. Phys. B 394 (1993) 509 [hep-lat/9209007] (\(\sqrt{K}\,a = 0.063(3)\)).

| β (lit) | \(a\sqrt{\sigma}\) | cite |
|--------:|-------------------:|------|
| 2.20 | 0.4690 | FHK92 T3 |
| 2.30 | 0.3690 | FHK92 T3 |
| 2.40 | 0.2660 | FHK92 T3 |
| 2.50 | 0.1905 | FHK92 T3 |
| 2.60 | 0.1360 | FHK92 T3 |
| 2.70 | 0.1015 | FHK92 T3 |
| 2.85 | 0.0630 | FHK92 T3 / UKQCD |

**Cross-checks (not primary knots):**

- Michael–Perantonis, J. Phys. G 18 (1992) 1725: \(Ka^2 = 0.0110(4)\) at β = 2.7
  ⇒ \(a\sqrt{\sigma} \approx 0.1049\) (P11 plan anchor; agrees with FHK 0.1015 within ~3%).
- Bali–Fingberg–Heller–Karsch–Schilling, PRL 71 (1993) 3059 [hep-lat/9306024]:
  \(a\sqrt{\sigma} = 0.1836(13)\) at 2.5115; \(0.0911(8)\) at 2.74.
- Bali–Schilling–Schlichter, PRD 51 (1995) 5165 [hep-lat/9409005]:
  \(Ka^2 \approx 0.0350 / 0.01458 / 0.00830\) at 2.50 / 2.635 / 2.74.

**Method at schedule βₘ:**

- Inside [2.20, 2.85]: linear interpolation of \(\ln(a\sqrt{\sigma})\) vs β (**interp**).
- Below 2.20 (j = 4): short extrapolation of that same ln-slope from β = 2.2–2.3
  (**extrap**); two-loop cross-check agrees to ~2%.
- Above 2.85 (j = 7, 8): universal two-loop SU(2) Wilson ratio from the β = 2.85
  anchor (**two-loop**); Λ cancels in ratios. Lit-slope continuation (AS-violating)
  is quoted only as an illustrative alternate.

Two-loop formula used (\(g^2 = 4/\beta\)):

\[
a\Lambda_L \propto (b_0 g^2)^{-b_1/(2 b_0^2)}\,\exp\!\bigl(-1/(2 b_0 g^2)\bigr),
\quad b_0 = 11/(24\pi^2),\; b_1 = 17/(96\pi^4).
\]

Known fact (same papers): bare-coupling asymptotic scaling is **not** restored
through β ≲ 2.85 (effective β-function ≈ 80% of two-loop). Absolute \(a\sqrt{\sigma}\)
at j ≥ 7 therefore carries an AS-violation systematic; **ratios** from two-loop are
the more robust continuum probe for the → 1/2 test.

### \(a(\beta_j)\sqrt{\sigma}\) along the schedule

| j | βⱼ | \(a\sqrt{\sigma}\) | source tag |
|---|---:|-------------------:|------------|
| 4 | 2.016 | 0.728 | **extrap** ln-slope from FHK 2.2/2.3 (2-loop alt ≈ 0.741) |
| 5 | 2.275 | 0.392 | **interp** FHK 2.2–2.3 |
| 6 | 2.533 | 0.170 | **interp** FHK 2.5–2.6 |
| 7 | 2.901 | 0.0554 | **two-loop** from FHK/UKQCD β = 2.85 (lit-slope alt ≈ 0.0537) |
| 8 | 3.159 | 0.0287 | **two-loop** from FHK/UKQCD β = 2.85 (lit-slope alt ≈ 0.0236) |

No fabricated table entries. j = 4 is the most uncertain (strong-coupling edge of the
lit window). j = 7–8 inherit the known AS-violation caveat.

## Ratios vs 1/2 and partial sums

\[
r_j = \frac{a(\beta_{j+1})\sqrt{\sigma}}{a(\beta_j)\sqrt{\sigma}},
\qquad
\delta_j = \bigl|\log_2(r_j) + 1\bigr|.
\]

| j → j+1 | \(r_j\) (lit/hybrid) | \(r_j\) (pure 2-loop) | \(\delta_j\) | target |
|--------:|---------------------:|----------------------:|-------------:|-------:|
| 4 → 5 | 0.538 | 0.524 | 0.105 | 0.5 |
| 5 → 6 | 0.434 | 0.522 | 0.203 | 0.5 |
| 6 → 7 | 0.326 | 0.394 | 0.619 | 0.5 |
| 7 → 8 | 0.518 | 0.518 | 0.050 | 0.5 |

Partial sums \(S_n = \sum_{k=4}^{n}\delta_k\):

| steps included | \(S\) |
|----------------|------:|
| 4→5 | 0.105 |
| 4→5,5→6 | 0.308 |
| 4→…→7 | 0.927 |
| 4→…→8 (= Σ_{j=4..7} δⱼ) | **0.977** |

### Tail (two-loop only, schedule β)

Under exact two-loop, \(A = 1.942\) is calibrated so \(\Delta\beta \sim 1/(2A)\) yields
\(r\to 1/2\) as \(j\to\infty\) (\(\beta\sim j/(2A)\)). Sketch of \(\delta_j\) on the schedule:

| j | \(r_j\) (2-loop) | δⱼ | cum from j=8 |
|--:|-----------------:|---:|-------------:|
| 8 | 0.516 | 0.046 | 0.046 |
| 10 | 0.514 | 0.040 | 0.129 |
| 12 | 0.512 | 0.035 | 0.202 |
| 15 | (κ-log jump) | — | ~0.64 |
| 20 | 0.508 | 0.024 | 0.771 |
| 30 | (κ-log jump) | — | ~1.35 |

Smooth steps approach 1/2 from above with δⱼ decreasing slowly; the κ⌊log₂(j+1)⌋
jumps produce finite bumps in δⱼ (by schedule design).

## Verdict (one paragraph; MC/lit only)

On this schedule the hybrid lit/two-loop ratios sit near 1/2 at the smooth ends
(j = 4→5 ≈ 0.54, j = 7→8 ≈ 0.52) but **undershoot** in the mid window
(j = 5→6 ≈ 0.43, j = 6→7 ≈ 0.33), the latter driven by the larger Δβ across the
first κ-log step plus known faster-than-two-loop running in the lit window.
The four-step partial sum \(S=\sum_{j=4}^{7}|{\log_2 r}+1|\approx 0.98\) is O(1), not
exploding. The two-loop tail decreases on smooth steps and only bumps at κ-log
thresholds, consistent with the schedule’s intent that \(r_j\to 1/2\) and that
\(\sum\delta_j\) stay controlled — **but this is an empirical/literature consistency
check, not a proof of summability**. AS violations through β ≈ 2.85 mean absolute
\(a\sqrt{\sigma}\) at j ≥ 7 are uncertain; ratio tests are the more trustworthy probe.

**Explicit disclaimer: MC / published lattice literature only — not a proof.**

## Bibliography

1. J. Fingberg, U. Heller, F. Karsch, *Scaling and asymptotic scaling in the SU(2)
   gauge theory*, Nucl. Phys. B 392 (1993) 493–517 [hep-lat/9208012].
2. S.P. Booth et al. (UKQCD), *SU(2) potentials from large lattices*,
   Nucl. Phys. B 394 (1993) 509 [hep-lat/9209007].
3. C. Michael, S.J. Perantonis, *Potentials and glueballs at large beta in SU(2)
   pure gauge theory*, J. Phys. G 18 (1992) 1725.
4. G.S. Bali et al., *The spatial string tension in the deconfined phase of
   (3+1)-dimensional SU(2)*, Phys. Rev. Lett. 71 (1993) 3059 [hep-lat/9306024].
5. G.S. Bali, K. Schilling, C. Schlichter, *Observing long colour flux tubes in
   SU(2) lattice gauge theory*, Phys. Rev. D 51 (1995) 5165 [hep-lat/9409005].
6. C. Michael, *The running coupling from lattice gauge theory*,
   Phys. Lett. B 283 (1992) 103 [hep-lat/9205010] (√σ/Λ estimates; AS context).

## Files

- `af_nome_asqrt_schedule.py` — regenerates table + ratios
- `af_nome_asqrt_table.csv`, `af_nome_ratios.csv` — numeric output
- This note: `AF_NOME_ASQRT_SCHEDULE.md`
