# Route repoint to the A03 direct-response alternative

Date: 2026-10-05 UTC. Four new Lean modules (21 public declarations) were
checked, plus a Monte Carlo sanity study. Nothing closes, and the chart is
unchanged. The A03 row (`docs/PROJECT-STATUS.md`, "Complete signed cost
versus SAME interacting variance on a justified scaling family") stays OPEN.
This audit records why the signed-cost/window-budget route to its target is
deprioritized and makes the row's existing "direct response alternative" the
working route.

## Mathematical result and scope

Let `R(n) = B x (T n x)` be the completed response of a completed vector `x`
on the SAME literal-width all-nome completion.

1. Completed Cauchy-Schwarz and even-grid log-convexity:
   `R(m+n)^2 <= R(2m) R(2n)`, `R(2u)^2 <= R(0) R(4u)` and `R(2n) >= 0`.
   (`BF4WilsonAllNomeCompletedLogConvexity.lean:101,107,116,125`)
2. Survival compiler. A positive rational norm floor together with ONE
   survival floor `kappa*R(0) <= R(2u)` gives `kappa*R(2u) <= R(4u)`
   (`:133`, `macro_ratio_of_survival_floor`). For the literal norm-one dyadic
   unit excitation, with `side scale = 2u`, the output is exactly the `hratio`
   input of `BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`
   `normalizedAnchorResponse_block_floor` (`:147`,
   `dyadic_macro_ratio_of_survival_floor`).
3. Even-lag Jensen and block compilers. A relative two-step floor
   `rho*R(0) <= R(2)` gives `rho^n R(0) <= R(2n)` and
   `rho^u R(2u) <= R(4u)`. If `(1-t)R(0) <= R(2)`, `L*t <= 1/2` and `u = L*k`,
   then `(1/2)^k R(2u) <= R(4u)`. When `t <= c/u`, this gives a
   side-uniform kappa of about `4^(-c)`.
   (`BF4WilsonAllNomeEvenResponseJensen.lean:114,139,154`)
4. Necessary rate screen. For a vacuum-orthogonal vector, any macro ratio
   (and therefore the window budget of `aggregate_window_macro_ratio`, and the
   ORIGINAL eventual budget `BF4WilsonAllNomeWindowSignedCost.lean:245`) forces
   `kappa*R(2u) <= twoStepRate^u * R(2u)`.
   (`BF4WilsonAllNomeWindowBudgetRateScreen.lean:49,67,77`)
5. Observed-loss circularity guard. Substituting the exact split `D = I + 4*O`
   into the exact energy/companion identity cancels the increment:
   `(1+beta)(4E+I) = 4(a(1-beta)-4k)M + 4k(4Z-U) + (k/2)(4*O)`. So observed
   loss and endpoint energy are interchangeable by an identity, and
   Ward/observed-loss payments supply no new estimate.
   (`BF4DyadicWilsonSquareObservedLossCircularity.lean:61,84`)

Scope: items 1-3 are compilers, and items 4-5 are screens. NO survival floor,
relative-energy floor, changing family, scaling or continuum statement is
supplied. Cauchy-Schwarz for the one-step form `(y,z) -> B(y, T z)`,
odd-lag log-convexity and the odd Jensen bound `R(n)R(0)^(n-1) >= R(1)^n`
are NOT proved. They need finite-level/intrinsic PSD of the twisted pairing.

## Routes deprioritized, with evidence

| # | Route | Evidence | Status |
|---|---|---|---|
| 1 | Endpoint-energy / observed-loss (Ward) payment | Item 5. Kernel-checked identity, so any such bound is the endpoint-energy bound restated | identity-only, no estimate |
| 2 | Fixed-nome sign windows (`k = 2x^3-1-x^8 >= 0`, alpha window, proven k-window) | Matched nome w = 0.783-0.804 at beta 2.3-2.6 (ASSUMED convention w^3 = I2/I1). x = w^(4l) = 0.375-0.419 at l=1 and 0.02-0.03 at l=4; k >= 0 needs x >= 0.879, and k <= -0.85 throughout. (1-w)4l = 0.78-3.5 (window needs <= 0.4). (1-w)128l = 25-111 (needs <= 1). Minimal beta for k >= 0 is about 15.8*side (alpha window: 5.2*side; proven window: 64*side), while fixed physical size needs only beta ~ 0.37 ln(side) (asymptotic freedom) | incompatible with any fixed-physical-size trajectory |
| 3 | Linear variance credit | Existing `audits/AUDIT-ORIGINAL-LINEAR-CREDIT-COLLAPSE-2026-10-04.md`: `rho(w,n) <= 4^(-n)` for every strict nome | collapses geometrically |
| 4 | Joint window budget on the literal padded square | MC below: correlator proxy kappa_b at s=2 is -0.73 to -0.83 (+-0.05) at all four beta (raw, local). It stays negative for smeared local loops (e.g. -0.18+-0.04 at (2.6, s=4)). It turns positive only for the smeared zero-momentum state at beta 2.6. In a single-exponential model, the budget overcounts the loss by 2/(1+e^(-am)): at u=1, kappa_b > 0 iff am < ln 2. The overcount tends to 1 as am -> 0 at fixed amu, so the budget is not dead in principle, but it is strictly stronger than the direct ratio it implies (`aggregate_window_macro_ratio`) | deprioritized. Not refuted for smoothed states |
| 5 | Width-dependent spectral / mixRate route | Item 4 plus `mixRate = 1-(headFloor/prefixCap)^(3 width^3)`. log2(headFloor/prefixCap) is about -10, -23 and -48 at w = 1/2, 4/5, 9/10 (Lean `#eval` of Nat.log2 of the numerator and denominator), so mixRate is about 1-2^(-69 width^3) at w = 0.8 | vacuous screen. A useful version must be width-uniform |

## Repoint (working route under the SAME A03 row)

Direct-response alternative: prove ONE survival floor `kappa*R(0) <= R(2u)`
with `side = 2u`, or a relative-energy floor `eps = 1-R(2)/R(0) <= c/side`
(block compiler, kappa about 4^(-c)). Do this for an explicit smoothed or
coherent state on an explicit trajectory (beta(side), side) of fixed physical
size. Items 2-3 then deliver the `hratio` of the existing normalized macro
ratio with no further loss. The work is split: P3 (smoothed coherent-state
construction) and P4 (numerics) are separate tracks.

## Monte Carlo evidence (numerical only; not a proof input)

Setup: L=16^4, SU(2) Wilson, heatbath + 4 OR, 3000 measurements every 4
sweeps, 60 jackknife bins. F = Tr of the spatial s x s loop. Smearing is
APE (alpha 0.5, 20 steps). Bundle with sources, run logs, binary hashes and
the full table: `computations/ym_direct_response_mc_2026_10_05/`
(`summary.txt` reproduces bit-for-bit from the binaries via `summary.py`).

Along the fixed-physical-size trajectory (2.4, s=2), (2.5, s=3), (2.6, s=4):

| state | R(2s)/R(s) | R(s)/R(0) (survival) | eps = 1-R1/R0 |
|---|---|---|---|
| raw local, s=2 at beta 2.3-2.6 | 0.013-0.023 (+-0.026) | 1.6e-3 to 1.8e-3 | 0.97 |
| APE-20 local | 0.103+-0.008, 0.106+-0.012, 0.169+-0.032 | 0.047, 0.036, 0.025 | 0.83, 0.73, 0.67 |
| APE-20 zero-momentum | 0.128+-0.046, 0.147+-0.058, 0.344+-0.068 | 0.104+-0.005, 0.101+-0.006, 0.110+-0.008 | 0.72, 0.57, 0.49 |

Raw local s=1: R(2)/R(1) = 0.036-0.053 (+-0.002), and 1-R1/R0 = 0.97-0.998.
The raw CS floor R(s)/R(0) is about 1e-3 at s=2 and 1e-4 at s=3, so the
literal padded square has essentially no survival. The smeared
zero-momentum survival is flat (about 0.10) along the trajectory. That is
the behavior a survival floor needs. eps*s is NOT constant at fixed lattice
smearing, so the smoothing radius must scale with side (P3/P4).

Window proxy kappa_b at s=2 for APE-20 zero-momentum: -0.31+-0.09 (2.4),
-0.03+-0.04 (2.5), +0.168+-0.035 (2.6). At (2.6, s=4): +0.15+-0.09.

Caveats: lag 8 on L=16 wraps halfway around and can inflate R(8)/R(4) up to
2x. Smearing is fixed in lattice units. The nome matching w^3 = I2/I1 used
for route 2 is an assumed convention. Raw s >= 3 entries are noise dominated.

## Forward/backward connection

Backward: consumes `BF4WilsonAllNomeCompletedGap`,
`BF4WilsonAllNomeCauchySchwarz`, `BF4WilsonAllNomeDyadicUnitExcitation`,
`BF4WilsonAllNomeWindowSignedCost`, `BF4DyadicWilsonSquareCompanionDeficit`,
`BondMovingRetuneFix` (Bernoulli) and `FiveHolonomyPerronCutoff`.
Forward: `dyadic_macro_ratio_of_survival_floor` feeds the `hratio` of
`normalizedAnchorResponse_block_floor`. The missing input is the survival or
relative-energy floor on a justified family (A03, OPEN).

## Verification

All checks used `scripts/safe_lean_build.py --check-worker-limit-gib 8 --check
<file> --check-output <olean>` with `LEAN_NUM_THREADS=2`, run sequentially on
the Mac. Each check ran under a resource monitor (pre-run vm_stat,
memory_pressure, `sysctl vm.loadavg`, `top -l 1`, then sampling every
0.5-10 s, with abort on pressure level >= 2 or available memory < 8 GiB).
Axiom gate: every declaration depends only on [propext, Quot.sound], with no
sorry and no errors.

| module | decls | wall | max RSS | min avail | source SHA256 | log SHA256 |
|---|---|---|---|---|---|---|
| BF4WilsonAllNomeCompletedLogConvexity | 9 | 7.2 s | 1.32 GiB | 21.48 GiB | cd5952220208790ae028aeba27aa3d734a8b0c271996360103c771523684fe1b | 725d1085282b8ab6064b669e111a57bb0db4fef4a20f9592677e639aef4ceb0d |
| BF4WilsonAllNomeWindowBudgetRateScreen | 3 | 2.2 s | 1.33 GiB | 21.48 GiB | b8ba412f3be0cd534a7a8aaf202a54bbefc5018e6fa06a84c825f0cbac10c908 | d8fabdc5cf3b4ea4dc6a3a3889b1d375b3585259f36c7e2948fcce101da2b9d7 |
| BF4DyadicWilsonSquareObservedLossCircularity | 2 | 1.7 s | 1.34 GiB | 20.88 GiB | 5d52acb708eb2b9e8538b534d4552c83cc3c1c498a114e818effb13b0688b453 | e62b76d4c00faf2d01f642ec4e993dfb51d5e545cfc61a12e6f25eb0829c49ca |
| BF4WilsonAllNomeEvenResponseJensen | 7 | 2.2 s | 1.32 GiB | 20.93 GiB | 3b5f08e0b62c8a302279b63b5106ee4bb5da61bff76d760cd5c5f0259f383259 | f01e047006231375f8be1f30295b8930a0e6966d48fd2cf71aa0a5abaa445413 |

Logs (Mac, outside the repo): `~/ymbot_scratch/lean_final_<module>.log`, with
resource logs at `~/ymbot_scratch/resource_final_<module>.log`.
`python3 scripts/lean_import_guard.py` reports the four new modules reachable
from the root with no import cycles. Its overall rc=1 comes from 444
unexpected semantic orphans that already existed (for example
`YMGap.RG.ScaleDependentGroupedContraction`, last touched 2026-07-24). These
are unrelated to this change. A full root build was not run (by policy).
