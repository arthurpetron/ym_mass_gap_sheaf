# P8: PathShiftedWindowSurvival on the exact Lean anchor Y_j (PARTIAL; P7 pass is still running)

- **Anchor definition:** see `P8_ANCHOR_DEFINITION.md`. Y_j is the vacuum-centered, unit-coefficient sum of ALL unsmoothed spatial fundamental plaquettes on one timeslice (cube side_j^2, padded by one layer), with a one-sided time box M_j = side_j:
  - R_Y(n) = (M+1)^-2 Σ_{a,b≤M} R_x(n+a+b)
  - W = R_Y(side+1)/R_Y(side//2)
- **Code:**
  - `p4run --measure-cfgs <list>` loads saved f32 configs, re-unitarizes them, and appends one record per config. It is resumable.
    - Validated: reproduces P7 record #3 from cfg_00003 to 1.3e-6 relative (flow rho=1 loops) and 5e-8 (raw loops); f32 max ||q|-1| = 5e-8.
    - The side-1 loops are the per-timeslice zero-momentum plaquette sums; they match an independent numpy computation to 1e-14.
  - `ana/p8_anchor.py` builds R_x, R_Y, W (E1 and E3d), m_eff, and λ0 from the flow/NS channel. It also gives a factorization estimate of the plaquette ground-state overlap: f0_x = R_xF(n)^2/(R_FF(2n) R_xx(0)), with F the smoothed loop.
- **Earlier beta 2.95/3.0 runs:** their data.bin holds only smeared side 7-11 loops and the lattice-AVERAGE spatial plaquette per level. There are no per-timeslice plaquette sums, so Y_j's correlator cannot be built (each run kept only one final config). Only the beta=2.50 runs (P4 1000 meas and P5 600 meas, both 24^3x32, sides 1,2,3) contain side-1 = plaquette timeslice sums; they were analyzed.
- **Tables:** `P8_ANCHOR_val_b2.50_L16x32.md` (regenerated seed 2501), `P8_ANCHOR_p4_b2.50_L24x32.md`, `P8_ANCHOR_p5_b2.50_L24x32.md`, `P8_ANCHOR_b2.95_L48x48_partial.md`.

## Preliminary results (beta 2.5; jackknife errors; E1 = vacuum-subtracted, E3d = subtraction-free)

| side | W on Y_j (E1) | W on Y_j (E3d) | W flow rho=1 | W NS-k2 | W flow rho=1 + same box | m0 a (flow, multi-lag) |
|---|---|---|---|---|---|---|
| 2 | val16: 0.20(33); P4: 0.25(14); P5: -0.07(21); **weighted 0.16(11)** | -0.26(27); 0.15(17); 0.09(14) | 0.207(36); 0.166(24); 0.215(30) | 0.208(36) | 0.270(86); 0.249(51); 0.291(56) | 0.65(14); 0.82(12); 0.57(12) |
| 3 | val16: 0.53(47); P5: -0.06(42) | 0.16(36); -0.09(17) | 0.142(31); 0.144(24) | 0.142(31) | 0.23(10); 0.245(76) | 0.58(10); 0.53(11) |
| 4 | val16: 0.50(68) | 2.0(60) | 0.171(54) | 0.169(54) | 0.55(16) | 0.56(14) |
| 5 | val16: 0.46(79) | -0.4(14) | 0.040(64) | 0.040(64) | 0.65(19) | 0.85(58) |

Ground-state overlap (val16, factorization through the side-s smoothed loop F):

| ref side | f0_x (plaquette sum, before box) | box gain g0^2 | f0_Y(0) (after box) | f0_Y(s/2) | spectral floor f0_Y(0)·λ0^(s+1) |
|---|---|---|---|---|---|
| 2 | 0.081(13) | 0.36(6) | 0.21(5) | 1.2(5) | ≈0.03 |
| 3 | 0.036(7) | 0.26(4) | 0.12(3) | 0.6(4) | ≈0.02 |
| 4 | 0.016(7) | 0.19(5) | 0.06(3) | 0.2(3) | ≈0.004 |
| 5 | 0.014(7) | 0.08(6) | 0.03(3) | 0.06(12) | — |

P4/P5 at 24^3 give f0_x = 0.086(8), 0.102(11) (ref side 2) and 0.046(6) (ref side 3). The estimate falls as the reference loop gets purer. The plaquette's true ground-state overlap at beta 2.5 is ≈ 1.5-3.5%. The box raises the lag-0 ground fraction by a factor of ≈ 3.

## Preliminary verdict
- **Directly measured, W on Y_j is not resolved.** Single datasets give |W| errors of 0.14-0.8. The combined side-2 value, 0.16(11), is consistent both with the flow-loop W (≈0.2) and with zero. There is no sign of collapse, but also no positive measurement. The MC limitation is "overlap too small": R_Y(side/2) carries ≈ f0_x·e^{-m·side/2} ≈ 1% of R_x(0), well below the per-config noise. "Side too long versus correlation length" is not the issue: the flow/NS channels at the same sides have W ≈ 0.15-0.2.
- **Spectral expectation (heuristic, not MC).** The window starts at lag side/2, a fixed physical time. UV states are exponentially gone there, so W depends only on the physical part of the plaquette spectral function, which has a continuum limit.
  - For a pure short-distance tail R_x(t) ∝ t^-5 (dim-4 operator, zero momentum), the boxed window is side-independent in the continuum: W → 0.105. On the lattice it is 0.007, 0.023, 0.049, 0.072 at side 2, 4, 8, 16.
  - So W on Y_j should stay bounded away from 0 along the trajectory, though plausibly at a few % to ≈0.1, below the smoothed loop's W.
  - The lag-0 overlap f0_Y(0) does decrease with the side (the plaquette is a UV operator; the box gives only ≈3x). Only the shifted window survives.
- **beta 2.95 (P7 configs):** 11 configs give pure noise for Y_j. NS-k2 and flow rho=1 agree exactly on the same configs (W = 0.31(46) at N=11). A full pass needs the ~26 configs available after the P7 interim (≈09:00 PT) and the final ~80 (≈12:00 PT). Even then Y_j's W is expected to stay unresolved; only f0_x via factorization may resolve, down to ≈0.003.
