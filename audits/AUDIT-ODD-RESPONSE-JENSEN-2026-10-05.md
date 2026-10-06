# Odd half of the response Jensen chain on the all-nome completed carrier (P2 odd)

One final focused check passed. This step proves the twisted (one-step)
Cauchy--Schwarz inequality, odd-lag and full consecutive log-convexity, the
odd Jensen chain, and a one-step block compiler. It also proves an
unconditional radius-uniform comparison for the smoothed state. Two open
inputs are stated as named `Prop`s and nothing proves them. The unchanged
whole-project goal is still continuum Yang--Mills on R^4 for every compact
simple group, with same-theory QFT axioms and a positive physical mass gap.

## Mathematical increment and actual consumers

Write R(k) = B(x, T(k) x) on the all-nome completion and S for the EXISTING
completed square root (`BF4WilsonAllNomeSquareRoot.squareRoot`), with
`squareRoot_pairing : B(S y, S z) = B(y, T(1) z)`. So the one-step pairing is
a plain completed pairing, it is PSD (`completedInner_oneStep_nonnegative`),
and it is symmetric (time balance). This step adds no new form, carrier or
operator. Proved:

- Twisted CS: B(y,T1 z)^2 <= B(y,T1 y) B(z,T1 z). This is P1's
  `completedInner_cauchySchwarz` applied to (S y, S z).
- Odd-lag log-convexity: R(m+n+1)^2 <= R(2m+1) R(2n+1). Take y = T(m)x and
  z = T(n)x.
- Full consecutive log-convexity: R(k+1)^2 <= R(k) R(k+2) for EVERY k. The
  even k case is P1 `response_log_convex`; the odd k case is the twisted CS.
- Odd Jensen chain, run through the even half's generic engine
  (`rc_logconvex_ratio_floor` / `rc_logconvex_geometric`, reused and not
  duplicated). Given rho*R(0) <= R(1) and a rational norm floor:
  - the ratio floor rho*R(n) <= R(n+1) at every lag;
  - rho^n R(0) <= R(n);
  - rho^j R(n) <= R(n+j);
  - the macro ratio rho^s R(s) <= R(2s) at ANY lag s, odd lags included.

  rho^n R(0) <= R(n) is the constructive cleared form of
  R(n) R(0)^(n-1) >= R(1)^n, the same convention as the even half: the
  literal form would need case splits on zero responses.
- Block compiler with a general Bernoulli constant. Assume s = L*k,
  0 <= t < 1, L*t <= delta < 1 and (1-t)R(0) <= R(1). Then
  (1-delta)^k R(s) <= R(2s). The energy form takes
  L*(R(0)-R(1)) <= delta*R(0) directly, with t = delta/L.
- Smoothed instance. Assume P3's open `SmoothedCoherentEpsBound M scale c0`,
  together with side = L*k, k > 0, c0 <= k*delta, 0 <= delta < 1, Nodup
  faces and sum c^2 > 0. Then `SmoothedMacroRatio M scale ((1-delta)^k)`,
  which is the line-132 `hratio` shape.
- Non-degrading comparison, unconditional: R_x(2M) <= B(Y_M,Y_M). The proof
  uses unit kernel mass and antitone responses. There is no (M+1)^-2 loss
  (contrast P3 `smoothedCoherent_norm_ge_family`).

## Constant comparison (rational powers; no exponential used)

Take eps = E_1/R(0) <= c/side, with side = L*k, so L*t <= c/k.

| Compiler | Constant |
| --- | --- |
| This file, delta = 1/2, k = 2c | (1/2)^(2c) = 4^(-c) |
| This file, general k | (1 - c/k)^k, which tends to e^(-c) as k grows (k = 4c gives (3/4)^(4c) = (81/256)^c ~ e^(-1.15c)) |
| `macro_ratio_of_block_energy` (even half) | half^k at lag 2u from a two-step floor. With t2 <= 2 t1 and u = side/2 this is also 4^(-c). It is stuck at delta = 1/2 because the hypothesis is `half <= 1 - L t`. |

The leading constant is NOT better than the even chain once the even
compiler is generalized the same way: both tend to e^(-c). What the odd chain
does gain:

- it consumes the one-step eps directly, with no two-step conversion;
- it works at any lag, odd included;
- it gives monotone ratios R(n+1)/R(n) >= rho;
- it gives a free delta, so for large c/side it beats the fixed 4^(-c).

Its survival constant is (1-delta)^k, not the e^(-2c) asked for. As k grows
it improves toward e^(-c), which is better than e^(-2c).

## Open inputs (named Props; nothing proves them)

```lean
def FamilyRadiusSurvival (M : Nat) (theta : Q') : Prop :=
  RCle (RCscale theta (B x0 x0)) (B x0 (T (2*M) x0))

def SmoothedCoherentNonDegradingFloor (M : Nat) (v : Q') : Prop :=
  RCle (Rq v) (B (Y M) (Y M))
```

Proved reduction: `FamilyRadiusSurvival M theta` with theta >= 0 gives
`SmoothedCoherentNonDegradingFloor M (theta * varianceFloor * sum c^2)`. This
is non-degrading exactly when theta is side- and M-uniform.

Screen: from a one-step floor, `familyRadiusSurvival_of_oneStep_floor` gives
theta = rho^(2M). That degrades unless 1 - rho = O(1/M). A side-uniform
theta for M ~ side is raw-family survival over 2M steps, of the same
difficulty as the eps bound for the unsmoothed family. So the
non-degrading floor is not obtained here.

| Declaration | Source | Role |
| --- | --- | --- |
| `boxSum_ge_const` | `lean/YMGap/Continuum/BF4WilsonAllNomeOddResponseJensen.lean:159` | Box sum >= mass * common lower bound. |
| `oneStep_form_nonnegative`, `oneStep_symmetric` | `:185,189` | PSD and symmetry of B(y,T1 z). |
| `oneStep_cauchySchwarz` | `:194` | Twisted CS via the completed square root. |
| `response_nonnegative`, `response_antitone`, `response_le_of_le` | `:204,236,242` | Positivity and monotonicity of R. |
| `response_odd_log_convex` | `:208` | R(m+n+1)^2 <= R(2m+1)R(2n+1). |
| `response_log_convex_step` | `:222` | R(k+1)^2 <= R(k)R(k+2) for all k. |
| `response_ratio_floor`, `response_odd_jensen`, `response_shift_floor` | `:251,272,294` | Odd Jensen chain from rho R(0) <= R(1). |
| `macro_ratio_of_oneStep_floor` | `:308` | rho^s R(s) <= R(2s), any s. |
| `macro_ratio_of_oneStep_block`, `macro_ratio_of_oneStep_block_energy` | `:317,339` | (1-delta)^k compiler (Bernoulli + block). |
| `smoothed_macroRatio_of_epsBound_odd` | `:391` | P3 eps bound gives SmoothedMacroRatio (1-delta)^k. |
| `smoothedCoherent_norm_ge_family_response` | `:426` | R_x(2M) <= B(Y_M,Y_M), unconditional. |
| `FamilyRadiusSurvival`, `SmoothedCoherentNonDegradingFloor` | `:451,457` | **OPEN** named Props. |
| `smoothedFloor_of_familyRadiusSurvival` | `:462` | Reduction to the non-degrading floor. |
| `familyRadiusSurvival_of_oneStep_floor` | `:476` | Screen: theta = rho^(2M) (degrading). |

## Verification boundary

Each Lean run went through `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 8 --check`. A wrapper refused to start while any
other Lean/lake/safe_lean_build process existed. A 10 s memory sampler was
set to abort on memory-pressure level >= 2 or available RAM < 8 GiB.

Accepted final run: exit 0, with no error, warning or sorry. All 19
`#print axioms` gates report `[propext, Quot.sound]`. The olean was emitted to
`lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeOddResponseJensen.olean`.
Peak load1 10.67, peak pressure level 1 (normal), minimum available RAM
22711 MiB, swap 0. Logs (Mac, outside repo):
`~/ymlean_prover_scratch/logs/check-p2oddfinal-20261005-200200.out` (SHA256
`2b0c412f63a61c786883239c55b4847aea99f1714f8ef1d755417c51e5e318d9`) and
`~/ymlean_prover_scratch/logs/mem-p2oddfinal-20261005-200200.log`.

Final source SHA256 (`BF4WilsonAllNomeOddResponseJensen.lean`):
`a3545aa574144b90b0595c870946293f8156f5ba5bbfd02b0cee6bcc5c6c4b26`.

Earlier scratch runs are not evidence for this source:

- p2odda failed because a stale copy was checked;
- p2oddb passed on the identical final source.

`scripts/lean_forbidden_token_scan.py` reported 0 executable hits. The import
is registered in `lean/YMGap.lean`, but registration is not root
verification. No full/root build, full audit, guard, broad metrics run or CI
was used. The commit adds no new sorry, axiom, classical shortcut,
noncomputable declaration, frontier change or replacement carrier.
