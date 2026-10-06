# AUDIT — H1 fixed-scale structure, H2 ⟹ H1, gap screen (2026-10-05)

File: `lean/YMGap/Continuum/BF4WilsonAllNomeH1FixedScale.lean` (557 lines).
SHA-256: `4119ee45ff289bacb5662f6d56fafeb641a0204d3687a4f2b05acf41a79e3f97`.
Paper companion: `audits/MATH-NOTE-H1-FIXED-SCALE-2026-10-05.md`.
Root registration: `lean/YMGap.lean`, imported right after
`BF4WilsonAllNomeGenericNormalizedAnchor`. Ledger entry dated 2026-10-06 UTC.

## Mathematical increment

All results are on the SAME all-nome completed Wilson carrier and for the SAME box-smoothed
coherent state `Y_M = (M+1)⁻¹ Σ_{k≤M} T^k x0` that the dyadic trajectory uses.

1. **Exact Fejér telescope.**
   `E_M = (M+1)⁻¹ (B(x0,Y_M) − B(T^{M+1}x0, Y_M))`, which is the identity
   `(1−λ)p(λ) = (1−λ^{M+1})/(M+1)` written at response level. The unconditional bound
   `(M+1)·E_M ≤ B(x0,x0)` follows.
2. **H2 ⟹ H1.**
   * At a fixed scale: `θB(x0,x0) ≤ B(Y,Y)` and `side ≤ c0θ(M+1)` give
     `SmoothedCoherentEpsBound`.
   * Along the path: `PathFamilyRadiusSurvival tr θ` and `1 ≤ c0θm` give `PathEpsBound tr c0`.
   * Consequently the full A03 normalized-anchor conclusion follows from H2 alone.
3. **Fixed-scale non-vacuity.** H1 holds at each scale with `c0 = side`.
4. **Gap screen.**
   * NEW OPEN Prop `WilsonVacuumRayleighRate r` (`B(y,Ty) ≤ r·B(y,y)` on the vacuum
     complement). It holds trivially at `r = 1`.
   * Such a rate gives `E ≥ (1−r)·B`.
   * Together with H1 it forces `side_j·(1−r_j) ≤ c0` at every scale, in rational form.

## Declarations

| Line | Declaration | Kind | Content |
|---|---|---|---|
| 261 | `boxSum_shift_telescope` | theorem | `Σ r f(k) − Σ r f(k+1) = r(f 0 − f(M+1))` over `boxKernel r M` |
| 275 | `boxSum_le_const` | theorem | box sum of terms `≤ a` is `≤ kernelMass·a` |
| 305 | `smoothedEnergy_telescope` | theorem | exact Fejér identity for `E_M` |
| 325 | `smoothed_tail_overlap_nonnegative` | theorem | `0 ≤ B(T^{M+1}x0, Y_M)` |
| 337 | `smoothed_head_overlap_le_norm` | theorem | `B(x0,Y_M) ≤ B(x0,x0)` |
| 356 | `smoothedEnergy_le_familyNorm` | theorem | `(M+1)E_M ≤ B(x0,x0)` |
| 372 | `smoothedEpsBound_trivial` | theorem | `SmoothedCoherentEpsBound M scale (side scale)` |
| 379 | `smoothedEpsBound_of_relativeFloor` | theorem | relative floor and `side ≤ c0θ(M+1)` ⟹ H1 at scale |
| 400 | `pathEpsBound_of_familyRadiusSurvival` | theorem | H2 and `1 ≤ c0θm` ⟹ `PathEpsBound tr c0` |
| 432 | `path_normalized_anchor_of_familyRadiusSurvival` | theorem | A03 anchor package (unit norm, block floors, real-time survival, increments) from H2 |
| 476 | `WilsonVacuumRayleighRate` | def : Prop | **OPEN for r < 1** |
| 481 | `wilsonVacuumRayleighRate_one` | theorem | non-vacuity at `r = 1` |
| 489 | `oneStep_energy_ge_of_rayleighRate` | theorem | `(1−r)B(y,y) ≤ B(y,y) − B(y,Ty)` |
| 501 | `epsBound_forces_rate_rc` | theorem | H1 + rate ⟹ `side(1−r)·B(Y,Y) ≤ c0·B(Y,Y)` |
| 515 | `epsBound_forces_rate` | theorem | rational form: `side·(1−r) ≤ c0` (distinct faces, nonzero coefficients) |
| 531 | `path_epsBound_forces_rate` | theorem | `∀ j, side_j(1−r_j) ≤ c0` from `PathEpsBound` and per-scale rates |

The private helpers are pointwise `RC` identities proved by `poly_identity_of_normal_eq`, a
rational cancellation against a positive floor (via `Int.le_total` on cross-products), and
local copies of standard lemmas.

## Open Props

* `WilsonVacuumRayleighRate r` for `r < 1`: new and OPEN. Nothing proves it.
* H1 (`PathEpsBound`) and H2 (`PathFamilyRadiusSurvival`) are unchanged and remain OPEN.
  This file proves only the implication H2 ⟹ H1.

## Honest strength

* The telescope identity and the energy bound are exact and unconditional, but they do not
  give H1 uniformly. Uniformity needs a relative floor (H2-type).
* H2 ⟹ H1 reduces two open hypotheses to one. H2 is at least as hard as H1. The math note
  argues that **both are heuristically false** for the unshifted box kernel on local
  plaquette families: the free-field `ρ ∝ ε⁴` UV weight gives `eps = O(1)`, with
  numerics `eps ≈ 0.95` for side 4 to 1024.
* The gap screen is rigorous on the Wilson carrier. Its application to the `w ≤ 1/2` cube
  rate and to `PathPhysicalContractionBand` needs a cube-to-Wilson rate bridge that the repo
  does not have. That part is paper-level only.
* Fixed-scale non-vacuity (`c0 = side`) is trivial by design. It shows that the Prop shape
  is not contradictory at one scale, and nothing more.

## Verification

* Monitored checks via `~/ymlean_prover_scratch/run_monitored_check.sh`
  (`safe_lean_build.py --jobs 1 --check-worker-limit-gib 8`, 10 s sampler):
  * `p8a` (20:34 PT): exit 0, peak_load1 12.85, peak_pressure_level 1,
    min_avail 18917 MiB.
  * `p8final` (20:37 PT, olean emitted): exit 0, peak_load1 12.61,
    peak_pressure_level 1, min_avail 17679 MiB. Log
    `~/ymlean_prover_scratch/logs/check-p8final-20261005-203730.out`.
* `#print axioms`: 16 of 16 gates report `[propext, Quot.sound]`. No errors, warnings or `sorry`.
* `python3 scripts/lean_forbidden_token_scan.py`: `executable_forbidden_hits 0`.
* The full-root `lake build` was not run (resource rules). The new module was checked
  against existing oleans, and its own olean is emitted.

## Numerics script (untrusted, heuristic support for the math note §2)

```python
import numpy as np
def eps(M, E, rho, shift=0):
    lam=np.exp(-E)
    p=np.where(E>1e-12,(1-lam**(M+1))/((M+1)*(1-lam)+1e-300),1.0)
    wgt=rho*p**2*lam**(2*shift)
    return np.trapezoid((1-lam)*wgt,E)/np.trapezoid(wgt,E)
E=np.linspace(1e-6,4.0,400001)
print("massless rho~E^4 on [0,4] lattice units, m=1 (M=side)")
for j in range(2,11):
    s=2**j; M=s
    print(j, s, "fejer eps*side=%.3g"%(eps(M,E,E**4)*s), "shift-side eps*side=%.3g"%(eps(M,E,E**4,shift=s)*s))
print("massive: threshold 2*mu*a, mu_phys=1, a=L/side, L=1")
for j in range(2,11):
    s=2**j; a=1.0/s; th=2*a
    rho=np.where(E>th,(E-th)**0.5*E**3,0.0)
    print(j, s, "fejer eps*side=%.3g"%(eps(s,E,rho)*s), "shift eps*side=%.3g"%(eps(s,E,rho,shift=s)*s))
print("fixed lattice gap E>=1 (strong coupling), shift: eps*side")
for j in range(2,11):
    s=2**j
    rho=np.where(E>1.0,1.0,0.0)
    print(j, s, "%.3g"%(eps(s,E,rho,shift=s)*s))
```

```python
import numpy as np, warnings
warnings.filterwarnings("ignore")
def eps(M, E, rho, shift=0):
    lam=np.exp(-E)
    p=np.where(E>1e-12,(1-lam**(M+1))/((M+1)*(1-lam)+1e-300),1.0)
    wgt=rho*p**2*np.exp(-2*shift*E)
    return np.trapezoid((1-lam)*wgt,E)/np.trapezoid(wgt,E)
E=np.linspace(1e-7,4.0,800001)
s=256
for L in [0.0625,0.25,1,4,16]:
    a=L/s; th=2*a
    rho=np.where(E>th,np.sqrt(np.clip(E-th,0,None))*E**3,0.0)
    print("L=%g shift eps*side=%.3g  (2*mu*L=%.3g)"%(L,eps(s,E,rho,shift=s)*s,2*L))
```
