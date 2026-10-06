# P9 multilevel (Lüscher–Weisz) pilot: time-sliced plaquette correlator, beta 2.5, 16^3x32 — 2026-10-06 (MC only)

Per-run detail: `P9_MULTILEVEL_PILOT_d4.md`, `P9_MULTILEVEL_PILOT_d3.md`.
Code: `src/main.rs` with `--ml-d d --ml-nsub n1,n2`; `p9_ml_run.sh`; analysis `ana/p9_ml.py`.

## Scheme
- **Freeze and sub-update.** Spatial links on timeslices t % d == 0 are frozen. Between level-0 configs (2 full sweeps apart), nsub sub-updates are run. Each sub-update is 1 heatbath + overrelaxation sweep of all other links.
- **What is accumulated.** For each slab, S1[t] = <P(t)> and S2[t,u] = <P(t)P(u)> are averaged over the sub-updates. Here P(t) is the timeslice spatial-plaquette sum, the Y_j operand.
- **Correlator from slab products.** For t, u in different slabs, C(t,u) = S1[t]·S1[u] (slabs are conditionally independent given the frozen boundaries). For t, u in the same slab, C(t,u) = S2[t,u].
- **"Interior pairs only" estimator.** Uses only pairs where neither slice is frozen, with vacuum subtraction by the matched pair-set means. By translation invariance it is unbiased. It agrees with the 5400-meas direct chain for every n: e.g. R(1..3) ×1e6 = 0.744(16), 0.131(14), 0.050(4) vs direct 0.738(22), 0.129(23), 0.051(22).
- **Cost accounting.** Equal-cost comparison against a plaquette-only direct chain (2 sweeps + measurement per config), using each run's own timings.

## Pilots
| pilot | threads | wall | configs | bins | s/config (nsub=40) |
|---|---|---|---|---|---|
| d=4 | 2 | 12:40–13:17 PT | 534 | 53 | 4.13 |
| d=3 | 1 | 12:48–13:17 PT | 233 | 23 | ≈7.5 |

d=3 is not a divisor of 32, so the last slab has thickness 2.

## Equal-cost variance-reduction factor (VRF > 1 means multilevel is better), interior-pairs estimator
| pilot, nsub | n=1 | n=2 | n=3 | n=4 | n=5 | n=6 | n=8 | n=10 | n=13 | **W s=2** | **W s=3** | W s=4 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| d=4, 10 | 0.9 | 1.4 | 5.9 | 12.6 | 7.0 | 4.7 | 6.1 | 5.1 | 5.3 | 5.2 | 3.0 | (22, denominator ≈ 0) |
| **d=4, 40** | 1.2 | 1.9 | 21 | 20 | 16 | 6.9 | 12.7 | 11.0 | 12.9 | **11.4** | **7.7** | (178, denominator ≈ 0) |
| d=3, 10 | 0.4 | 3.5 | 5.3 | 2.7 | 2.1 | 5.5 | 4.8 | 3.0 | 5.4 | 4.6 | 8.0 | — |
| d=3, 40 | 0.8 | 7.0 | 9.3 | 4.2 | 5.7 | 12.1 | 32 | 5.0 | 9.8 | 4.7 | 13.7 | — |

- Same-slab lags (n < d) gain nothing, as expected. Lags that cross a frozen boundary gain 5–30x.
- Going from nsub 10 to 40 still raised the VRF by about 2–4x at n ≥ 3, so nsub = 40 is not saturated.
- The pilot VRFs carry roughly ±30–40% uncertainty (53 / 23 bins).

## W on Y_j from the pilots (box M=side, interior-pairs, nsub=40)
| | W s=2 | W s=3 | W s=4 |
|---|---|---|---|
| ML d=4 (534 cfg, 37 min, 2 threads) | **0.112(25)** | 0.037(49) | 0.02(27) |
| ML d=3 (233 cfg, 29 min, 1 thread) | 0.127(62) | 0.154(58) | 0.54(22) |
| direct p8_hi, 5400 meas (E1 / E3d) | −0.08(11) / −0.015(63) | 0.02(18) / −0.13(8) | ill-defined |
| flow-loop rho=1 W (same ensemble) | 0.1678(88) | 0.1033(75) | 0.139(14) |

- The 37-min d=4 pilot already beats the 2-h direct chain's error at side 2 by 2.5x.
- It puts W(Y_j, s=2) at about 0.11(3): positive, but about 2σ below the flow-loop W. That fits the ground-state floor computed with the n=2 overlap, 0.12(3), and sits about 1.7σ below the floor computed with the n=1 overlap, 0.19(4).

## Cost to ±0.02 on W(Y_j) (d=4, nsub=40, 2 threads, scaled from the pilot)
| side | multilevel | direct plaquette-only | direct with flows (p8_hi rate) |
|---|---|---|---|
| 2 | **≈1 h** | ≈11 h | ≈69 h |
| 3 | **≈4 h** | ≈28 h | ≈170 h |
| 4 | ≈100 h (denominator R_Y(2) ≈ 0.01·R_Y(0)) | ≫100 h | — |

- With 4 threads, expect about 1.7x less wall time.
- One run serves all sides.

## Verdict and plan (NOT launched)
- **Sides 2–3: yes.** A single d=4 run with nsub checkpoints 40, 100 and 4 threads (≈4 GB headroom is ample: RSS 81 MB) of about 3–4 h wall should give ±0.02 at side 2 and about ±0.02–0.025 at side 3. The nsub=100 checkpoint tests whether the VRF keeps growing.
- **Side 4: no**, not within a few hours. Its denominator R_Y(2) is consistent with zero. It would need a nested two-level scheme (outer d=8 with an inner d=4 level, which squares the gain for lags ≥ 8). That is a code change, and the cost is unmeasured.
- d=4 is preferred over d=3: better at side 2, comparable at side 3 within pilot noise, and it divides Lt=32.

## Resources
| pilot | CPU | min MemAvailable | job RSS | max load1 | sampler pauses (PAUSE_MB 4000) |
|---|---|---|---|---|---|
| d=4 | 193% mean | 9.32 GB | 81 MB | 4.9 | 0 |
| d=3 | 98% mean | 9.27 GB | 79 MB | — | 0 |

- p8_hi (YM Bot's run) ended 12:45 PT, so total threads stayed ≤ 4 (p8_hi 2 + d4 2 until 12:45; d4 2 + d3 1 afterwards).
- Both pilots were stopped at 13:17 PT.
