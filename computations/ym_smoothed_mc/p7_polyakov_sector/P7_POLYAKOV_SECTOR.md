# P7 β = 2.95: Polyakov (torelon) sector vs 0⁺⁺, at Ls = 32 and 48

**MC only, not proof.** Effective masses are in lattice units with jackknife errors. Single-thread tool. P11 (pid 261428) was not touched.
Date: 2026-10-06/07 PT. Analysis: `p7_polyakov_sector.py` (full output in `p7_polyakov_sector_stdout.txt`).
Tool: `polysec_tool/` (Rust, one thread). Raw outputs: `/workspace/ymmc/p4_smoothed/runs/p7_polyakov_sector/`.

## What was on disk

| Ls | saved configs | Polyakov info saved by P7 |
|---:|---|---|
| 48 (48³×48, side 8) | **80** f32 configs (`cfg_00003…00240`, every 3rd of 240 meas = every 12 sweeps) | only the volume-averaged P_d per meas (no t-dependence), so no correlator |
| 32 (32³×48, side 8) | **none**, only the final f64 checkpoint `data.ckpt` | none (P6-format records, no Polyakov fields) |

The 0⁺⁺ correlators *were* saved at both Ls (240 meas each). These are per-timeslice, zero-momentum, flow-smoothed s×s spatial loops for s = 7, 8, 9, at ρ = √(6t)/8 = 0…1.5. They are reused directly here.

## What was run

- **Ls = 48:** measured the timeslice-resolved spatial Polyakov loops on all 80 saved configs. Streaming one timeslice at a time kept RSS at about 10 MB. Validation: the unsmeared spatial plaquette 0.717626 matches the P7 record E_s for meas 3 exactly. Time: 37.6 min.
- **Ls = 32:** minimal re-run, 1 thread, started from the saved equilibrated checkpoint (plaq 0.717567, which equals P7's last meas). 100 meas × 4 sweeps (1 heat-bath + 4 overrelaxation each), new seed 29517, measuring Polyakov loops after each block. Time: 36.7 min.
- **Smearing:** APE within each timeslice, α = 0.5, projected to SU(2), at levels n = 0/5/10/20/30. Results are quoted at n = 30, which has the best overlap: C(1)/C(0) = 0.78 (L48) and 0.89 (L32).
- **Operator:** P_d(t) = mean over the Ls² lines of ½Tr ∏ V_d, for d = 1, 2, 3. The correlators are averaged over the 3 directions.
- **Two estimators:**
  - *unsub*: ⟨P(t)P(t+τ)⟩. This is the center-symmetric choice, since ⟨P⟩ = 0 exactly in an ergodic ensemble.
  - *sub*: the same minus the sample ⟨P⟩².
- **Effective mass:** periodic cosh form. Plateau = jackknife mean of m_eff over a t-window, with 16 bins.

## Results

| | Ls = 48 | Ls = 32 |
|---|---:|---:|
| m_P unsub, t∈[3,8] | **0.083(5)** | **0.082(9)** |
| m_P sub, t∈[3,8] | 0.115(16) | 0.111(10) |
| m_P other windows (unsub / sub) | 0.099(5)…0.075(9) / 0.133(13)…0.112(27) | 0.083(7)…0.084(13) / 0.107(8)…0.124(17) |
| m_P dirs 1+2 only (unsub, [3,8]) | 0.091(9) | 0.080(12) |
| **m_P quoted (incl. estimator spread)** | **0.10(2)** | **0.10(2)** |
| m_0⁺⁺, flow ρ = 1.5, side 8, t∈[3,6] | **0.228(32)** | **0.225(28)** |
| m_0⁺⁺, t∈[4,8] | 0.211(39) | 0.227(42) |
| **m_P / m_0⁺⁺** (unsub / sub) | **0.36(6) / 0.50(10)** | **0.36(6) / 0.49(8)** |

The 0⁺⁺ m_eff still drifts down slowly at both Ls: 0.27 → 0.21 over t = 2…8 at Ls = 48. So m_0⁺⁺ ≈ 0.22(3) is an upper-side plateau estimate. Its expectation is μ·a√σ = 3.78(7) × 0.04884 = **0.185(3)**. This uses μ from LTW04 [hep-lat/0404008] and a√σ(2.95) from the a10b9ea4 module: two-loop from the FHK92/UKQCD β = 2.85 anchor (the AS-violating lit-slope alternative gives 0.0458).

## Torelon expectation (a²σ = 0.002385)

| Ls | L√σ | σL − π/(3L) | Nambu–Goto √ form | measured m_P |
|---:|---:|---:|---:|---:|
| 48 | 2.34 | **0.093** | 0.090 | 0.083(5)–0.115(16) ✔ |
| 32 | 1.56 | **0.044** | 0.029 | 0.082(9)–0.111(10) ✘ (about 2× heavier) |

At Ls = 48 the Polyakov channel agrees with the string formula. At Ls = 32 it does **not**: the measured mass is the same as at Ls = 48 instead of half of it. L√σ = 1.56 is only about 10% above the SU(2) deconfinement length 1/(T_c/√σ) ≈ 1.41, where the string description is not expected to hold. Even so, the sign of the deviation (heavier, not lighter) is **not understood**. Possible causes:
- the short single-chain re-run and slow modes (⟨P₁⟩ = −0.13 at L32);
- finite-volume distortion, which P7 already saw in ε·s at Ls = 32;
- the a√σ(2.95) systematic.

Treat the Ls = 32 Polyakov mass as unresolved.

## Effect on the headroom (sector minimum)

The all-vector rate is set by the minimum over sectors. At **both** volumes the Polyakov (center-odd, winding) sector is **lighter** than 0⁺⁺, so it sets the minimum:
m_min = m_P ≈ 0.10, about 0.36–0.50 × m_0⁺⁺.

If the ~64× halving-time headroom scales linearly with the gap (it was computed from 0⁺⁺ only), it shrinks by that factor to **about 23–32×**. It stays positive but is roughly 2–3× smaller.

This only applies if the Lean "all-vector" carrier includes the center-odd Polyakov/winding states, i.e. all gauge-invariant vectors on the periodic box. If the carrier is restricted to the center-even (contractible-loop) sector, the 0⁺⁺ value stands.

Volume dependence: the torelon mass grows like σL. It equals μ√σ at L√σ ≈ 4.04, which is **Ls ≈ 83 at β = 2.95**. So at any Ls below about 83 the Polyakov sector is the lighter one, and the gap minimum is a finite-volume quantity set by the box, not by the glueball.

## Caveats

- **P7's slow dir-3 sector mode.** The saved L48 configs inherit P7's dir-3 Polyakov ordering: P7 had 4 sign flips in 240 meas. On the 80 saved configs, dir 3 has ⟨P₃⟩ = −0.054 with 6 sign changes, against 17 and 8 for dirs 1 and 2. Because of this, dir 3 alone differs strongly between estimators: unsub 0.05–0.09 vs sub 0.10–0.21. That is why dirs 1+2 are also quoted. Errors are probably underestimated by about 1.5×, as in the P9 addendum.
- **L32 chain is short.** 100 meas from one checkpoint, so the 16 jackknife bins of 6 meas are probably correlated. Dir 1 sat at ⟨P₁⟩ = −0.13.
- **Estimator spread.** unsub vs sub differ by about 0.03, and that difference is included in the quoted ±0.02. Neither m_P nor m_0⁺⁺ has a clean long plateau.
- **Smearing.** APE n = 30 gives about 3–4 lattice units of smearing radius, well below the flux-tube width (~1/√σ ≈ 20a). Overlap is decent but not ideal.
- The 0⁺⁺ is a single smoothed-loop operator, not a variational basis, so it is an upper-side estimate.

**MC only, not proof.**

## Resources

- **Start (22:34 PT):** nproc 8; free −g 15 total / 10 used / 5 avail; load 4.36 4.07 4.11; MemAvailable 5.70 GB.
- **During the jobs (151 samples every 30 s, `resource_sampler.log`):** MemAvailable min / mean / max = 2.68 / 7.46 / 8.46 GB; load1 3.0 / 4.9 / 7.8.
- **One throttle event:** 22:42:49–22:44:19 PT, the job was **paused** (SIGSTOP) because another agent's Lean build pushed MemAvailable down to 2.81 GB. It resumed automatically at 5.0 GB.
- Peak job RSS: about 10 MB (L48), about 300 MB (L32).

## Citations

B. Lucini, M. Teper, U. Wenger, JHEP 06 (2004) 012 [hep-lat/0404008] (μ = 3.78(7)). J. Fingberg, U. Heller, F. Karsch, NPB 392 (1993) 493 [hep-lat/9208012]. UKQCD (Booth et al.), NPB 394 (1993) 509 [hep-lat/9209007]. a10b9ea4 `af_nome_asqrt`. Torelon LO and Nambu–Goto forms: Lüscher–Symanzik–Weisz NPB 173 (1980) 365; de Forcrand et al. PLB 160 (1985) 137.
