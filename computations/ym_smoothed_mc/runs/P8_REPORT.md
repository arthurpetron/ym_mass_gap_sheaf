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
