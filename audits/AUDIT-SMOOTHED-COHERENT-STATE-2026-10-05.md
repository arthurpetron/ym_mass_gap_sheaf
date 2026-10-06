# Smoothed coherent family state on the all-nome completed carrier (P3)

One final focused check passed. This step builds a state and its conditional
consumers. It does not prove an estimate. The open input is stated as a named
`Prop` and nothing proves it. The unchanged whole-project goal is still
continuum Yang--Mills on R^4 for every compact simple group, with same-theory
QFT axioms and a positive physical mass gap.

## Mathematical increment and actual consumers

Let x = `familyExcitation(width, qs, c)`. This is the EXISTING original
completed-state pin of the literal signed family `familySpan width qs c` in
the all-nome Wilson vacuum complement. Its opposite-incidence angular
geometry is in `BF4ExactSlabFixedSpatialFamilyCoherentEnergy`, which is
reused here. For an explicit smoothing radius M, this file defines

```
Y_M = sum_{m=0}^{M} (1/(M+1)) T(m) x        (orbitSum x (timeKernel M))
R_M(n) = B(Y_M, T(n) Y_M),   E_M = R_M(0) - R_M(1).
```

The construction adds no carrier, family, operator, or completion. The radius M
is a free `Nat`, so a schedule may let it grow with `side scale`.

Proved:

- Y_M lies in the actual vacuum complement.
- Y_0 = x exactly.
- T(n) commutes with the smoothing.
- R_M(n) is the explicit double kernel sum of the ORIGINAL centered family
  moments `centeredTimeMoment (m+k+n) familyState familyState`, with every
  signed cross term kept.
- The kernel weights are positive and their total mass is 1.
- R_M(n) >= 0 for every n, R_M decreases in n, R_M(n) <= R_M(0), and E_M >= 0.
- Unconditional norm floor: B(Y_M,Y_M) >= (M+1)^-2 B(x,x), and hence, for
  distinct faces, B(Y_M,Y_M) >= (M+1)^-2 * varianceFloor(w) * sum c^2.
  This floor gets worse as M grows. It is not a uniform floor.
- Same-carrier mirror of
  `BF4ExactSlabFixedSpatialJointEnergySurvival.response_floor_of_relative_energy`
  (line 112). That theorem lives on the JOINT exact-slab carrier, so it cannot
  be applied to an all-nome vector. The mirror has the identical hypothesis
  shape `n*delta+theta<=1` and is proved from the all-nome
  `time_loss_linear_bound`.
- Macro adapters:
  - `SmoothedMacroRatio` is the hypothesis shape `kappa*R(s)<=R(2s)` that
    `BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132` consumes, stated for
    Y_M.
  - Block floors follow through `response_shifted_block_geometric_lower`.
  - The landed P1 compiler `macro_ratio_of_survival_floor` gets its
    rational-norm-floor inputs from the unconditional floor above.

The OPEN input, stated and not proved:

```lean
def SmoothedCoherentEpsBound (M scale : Nat) (c0 : Q') : Prop :=
  RCle (RCscale (Q'.ofNat (side scale)) (smoothedEnergy hw0 hw1 width qs c hqs M))
    (RCscale c0 (B (Y M) (Y M)))
```

That is, side*(R_M(0)-R_M(1)) <= c0*R_M(0), i.e. eps <= c0/side. Given this
Prop, the checked consumers return:

- survival at lag side with any theta such that c0+theta<=1;
- the macro ratio with kappa such that c0+kappa<=1, when side=2u
  (linear loss plus P1 log-convexity);
- the macro ratio with 2*c0+kappa<=1 from linear loss alone.

| Declaration | Source | Role |
| --- | --- | --- |
| `smoothingWeight`, `timeKernel` | `lean/YMGap/Continuum/BF4WilsonAllNomeSmoothedCoherentState.lean:164,183` | Explicit radius-M normalized box kernel (computable data). |
| `timeKernel_weight_pos`, `timeKernel_mass` | same file `:202,228` | Positive weights; total mass ≈ 1. |
| `smoothedCoherentVector`, `smoothedCoherentState` | `:285,291` | Y_M on the SAME completion; vacuum-complement membership. |
| `smoothedCoherentVector_radius_zero` | `:308` | Y_0 = familyExcitation. |
| `smoothedResponse_orbit_expand`, `smoothedResponse_pin` | `:326,341` | Responses as kernel sums of the ORIGINAL family moments. |
| `smoothedResponse_nonnegative`, `smoothedResponse_antitone`, `smoothedResponse_le_norm`, `smoothedEnergy_nonnegative` | `:359,367,372,380` | Positivity and monotonicity. |
| `smoothedCoherent_norm_ge_family`, `smoothedCoherent_norm_floor`, `smoothedNormFloor_positive` | `:385,411,263` | Unconditional (M+1)^-2 norm floor. |
| `smoothed_response_ge_fraction_of_relative_energy`, `smoothed_response_floor_of_relative_energy`, `..._family` | `:422,437,451` | All-nome mirror of JointEnergySurvival:97/112, with the floor plugged in. |
| `SmoothedMacroRatio`, `smoothed_macro_block_floor`, `smoothed_macro_block_response_floor` | `:466,471,484` | Line-132 hypothesis shape for Y_M; geometric block floors. |
| `smoothed_macroRatio_of_relative_energy` | `:498` | Relative energy at lag 2s gives the macro ratio (linear loss). |
| `SmoothedCoherentEpsBound` | `:519` | **OPEN** named Prop, eps <= c0/side. |
| `smoothed_survival_of_epsBound`, `smoothed_survival_floor_of_epsBound` | `:524,536` | Conditional survival at lag side. |
| `smoothed_macroRatio_of_epsBound`, `smoothed_macroRatio_of_survival_floor`, `smoothed_macroRatio_of_epsBound_logConvex` | `:549,572,588` | Conditional macro ratio (linear; via P1 `macro_ratio_of_survival_floor`). |
| `zeroMomentumSmoothedState`, `zeroMomentumSmoothed_norm_floor` | `:606,609` | Instance: every spatial face with c=1 (`spatialFaces_nodup`). |

## Backward screening and remaining analytic estimate

The unconditional floor shrinks like (M+1)^-2. Feeding it to the relative-energy
compiler gives a response floor that degrades with radius. Useful
side-uniform control therefore has to come from `SmoothedCoherentEpsBound`
itself, together with a floor that does not degrade (for example
R_M(0) >= R_x(2M)), not from this floor. The Monte Carlo review
(`/workspace/reviews/YM-sanity-backtrack-2026-10-05.md`, box-side, not in the
repo) suggests eps falls with smoothing for the coherent family. That is
numerical evidence only. No absolute-energy smallness or kinetic-ceiling
consumer is used here.

`SmoothedCoherentEpsBound` fixes nome, width, family and radius at a single
scale. A path version (side=2^j, nome per asymptotic freedom, width >> side,
M_j growing) is P5/P6 and is NOT stated here. No frontier bundle, scorecard
or chart node changes.

## Verification boundary

Each Lean run went through `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 8 --check`. Before each run a process check confirmed
that no other Lean/lake process was active. A 10 s memory sampler was set to
abort on memory-pressure level >= 2 or available RAM < 8 GiB.

Accepted final run, exit 0 with no error, warning or sorry: 35 `#print axioms`
gates, each `[propext, Quot.sound]`. The olean was emitted to
`lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeSmoothedCoherentState.olean`.
Peak load1 13.66, peak pressure level 1 (normal), minimum available RAM
22024 MiB, swap 0. Logs (Mac, outside repo):
`~/ymlean_prover_scratch/logs/check-p3final2-20261005-195441.out` (SHA256
`7a264e5d171d24712313b3a77c70768cac577a0aa8b550983411be99e876d3ec`) and
`~/ymlean_prover_scratch/logs/mem-p3final2-20261005-195441.log`.

Final source SHA256 (`BF4WilsonAllNomeSmoothedCoherentState.lean`):
`26f4e632874d495f1f26ca0434318e36cd87f44ae7aa43e0fcf5e991383ca180`.

Earlier scratch elaborations are not evidence for this source:

- one run was refused by the lock while another worker held it;
- one run failed on notation/arguments;
- two passing scratch runs preceded a docstring-only edit.

`scripts/lean_forbidden_token_scan.py` reported 0 executable hits. The import
is registered in `lean/YMGap.lean`, but registration is not root
verification. No full/root build, full audit, guard, broad metrics run or CI
was used. The commit adds no new sorry, axiom, classical shortcut,
noncomputable declaration, frontier change or replacement carrier.
