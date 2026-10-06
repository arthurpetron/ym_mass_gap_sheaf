# Explicit dyadic smoothed-coherent trajectory and the two-hypothesis A03 compiler (P6 groundwork)

One final focused check passed. This step defines a trajectory as data and
proves conditional compilers. It does not prove an estimate. Every open input
is a named `Prop` and nothing proves any of them. The unchanged
whole-project goal is still continuum Yang--Mills on R^4 for every compact
simple group, with same-theory QFT axioms and a positive physical mass gap.

## Trajectory data

All of it lives on the EXISTING all-nome completed Wilson carrier. No carrier,
family, operator or completion is added.

- `side j = 2^j` (the existing `BF4DyadicWilsonSquare.side`).
- `trajRadius m j = m * side j` (`M_j`, proportional to side, with factor
  `m > 0`).
- `trajWidth j = side j * side j + 1`. Proved: `side j < width_j` and
  `side_j^2 < width_j`.
- `NomeSchedule` is ABSTRACT. It records the nome sequence `w_j` together with:
  - `0 < w_j < 1`;
  - `w_j <= w_{j+1}`;
  - an explicit modulus with `1 - eps <= w_j` beyond `limitModulus eps`.

  No asymptotic-freedom formula is hardcoded. `dyadicNomeSchedule`
  (`w_j = 1 - 2^-(j+1)`) shows the interface can be inhabited; it is not a
  physical schedule.
- `NomeScheduleAFJustified ns` is the **OPEN** physical justification. It asks
  that the schedule match some `AFRateCalibration.AFRateModulus` (the existing
  two-sided AF interface).
- `DyadicSmoothedTrajectory` bundles:
  - the schedule and the radius factor;
  - the face lists `faces j`, all spatial faces at `width_j` and distinct;
  - coefficients `coeff j` with positive mass `sum c^2`.

  From these, `state j = Y_{M_j}` (P3's smoothed coherent vector at
  `(w_j, width_j)`) and `familyVector j = x_j`.

## The conditional theorem and its exact hypotheses

```lean
theorem path_macro_conclusion (tr : DyadicSmoothedTrajectory) (c0 theta delta : Q') (a : Nat)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta)
    (H1 : PathEpsBound tr c0) (H2 : PathFamilyRadiusSurvival tr theta) :
    ∀ j : Nat, a ≤ j →
      tr.MacroRatioAt j (((1 : Q') - delta)^(side a)) ∧
      ∀ i : Nat, RCle (RCscale ((((1 : Q') - delta)^(side a))^i * theta) (tr.familyNorm j))
        (tr.response j (side j * i))
```

The two OPEN path-uniform hypotheses:

```lean
def PathEpsBound (tr : DyadicSmoothedTrajectory) (c0 : Q') : Prop :=
  ∀ j, SmoothedCoherentEpsBound (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j) j c0

def PathFamilyRadiusSurvival (tr : DyadicSmoothedTrajectory) (theta : Q') : Prop :=
  ∀ j, FamilyRadiusSurvival (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (trajWidth j) (tr.faces j) (tr.coeff j) (tr.faces_spatial j) (tr.radius j) theta
```

Everything else in the hypothesis list is a scalar choice of constants: `a`,
`delta` and the condition `c0 <= 2^a delta`. No sign condition on theta is
needed.

Conclusion at every scale `j >= a`:

- (i) the SAME macro ratio `kappa = (1-delta)^(2^a)` at `Y_j`, which is the
  line-132 `hratio` shape. This part comes from H1 alone (`path_macroRatio`).
- (ii) the scale-uniform physical-time floor
  `kappa^i * theta * B(x_j,x_j) <= R_j(side_j * i)` for every `i`. Time `i` is
  in units where `spacing * side = 1`.

`path_macro_conclusion_absolute` is the same result with H2 replaced by
`PathNonDegradingFloor tr v` (the absolute `SmoothedCoherentNonDegradingFloor`
with one v for all j). `pathNonDegradingFloor_of_familyRadiusSurvival` derives
that from H2 plus the scalar condition `PathVarianceMassFloor tr theta v`.

## Consumers that need more: named extra Props

- **Dyadic-unit A03 consumer.** The consumer at
  `BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`
  (`normalizedAnchorResponse_block_floor`, and with it the real-time increment
  theorems) is hard-wired to `dyadicUnitExcitation`, not to `Y_j`.
  `path_unit_anchor_floor` feeds it from H1 together with the OPEN
  `PathUnitRatioBridge tr kappa kappa'`. That bridge says the smoothed ratio at
  scale j implies the unit-state `hratio` on the same `(w_j, width_j)`.
  **Hidden strength:** nothing relates `Y_j` to the unit state, so the bridge
  carries ALL of the unit-state A03 content.
- **B04l** (`BF4PhysicalChangingNomeDynamicFamily`). It lives on the physical
  cutoff cube carrier, not this one, so no consumer there takes `Y_j`.
  - `trajectoryDynamicFamily` fills its nome slot from this trajectory and its
    spacing slot with `2^-j` (`dyadicSpacingToZero`).
  - Its per-scale contraction slot is the OPEN `PathCubeContraction ns`. The
    existing producer `completedSectorContraction` needs `w <= 1/2`.
  - `nomeSchedule_eventually_not_le_half` proves that every `NomeSchedule`
    eventually leaves that range.
- **B04q.** This is a scalar target `L <= s_n(2+6H(w_n)) <= U` on the same
  cube carrier, with the pulled-kernel minimum F still unestimated. It does not
  involve `Y_j`; nothing is instantiated.

## Honest strength assessment

- **The nome schedule is not used.** Its monotonicity and limit fields, and
  `NomeScheduleAFJustified`, are consumed by NO theorem here.
  `path_macro_conclusion` holds for any nome sequence. All the physics sits in
  H1.
- **H1 is scale-invariant and is not known to be vacuous or contradictory.**
  `path_rate_screen` shows that H1 hides
  `kappa R_j(side) <= twoStepRate(w_j,width_j)^(side_j/2) R_j(side)`. Since
  `twoStepRate` is volume-exponentially close to 1, that screen does not bind.
  At FIXED nome, H1 (eps_j <= c0 2^-j) is not expected physically, so H1
  implicitly requires `w_j -> 1` at the right rate. That requirement is not
  checked here.
- **The constants do not degrade.** `kappa = (1-delta)^(2^a)` is independent of
  j. With `delta = c0/2^a` it tends to `e^(-c0)` as `a` grows; `a = 1`,
  `delta = c0/2` gives `(1-c0/2)^2`. The only restriction is `j >= a`.
- **H2 is as hard as the problem it helps with.** It is raw-family survival over
  `2 M_j = 2m side_j` steps. That is of the same difficulty as an eps bound for
  the UNSMOOTHED family: from a one-step floor it holds with `theta = rho^(2M)`.
  Smoothing buys nothing for the floor. H2 is not used for (i).
- **H2' is close to free.** The absolute floor is NOT invariant under rescaling
  `coeff j`, because `R` scales by `lambda^2`. A free family schedule can meet
  any v. P3's unconditional floor `(M_j+1)^-2 varianceFloor(w_j) sum c_j^2` can
  even grow with j (for example all faces with c=1, where `sum c^2` grows like
  the face count) unless `varianceFloor(w_j)` collapses. So only the relative
  H2 is a meaningful hypothesis, and it is the one used in the main theorem.

## Even-compiler generalization

`macro_ratio_of_twoStep_block_general` / `..._energy_general` (in this file;
the even-half file is unchanged):

- Hypotheses: `u = L*k`, `L t <= delta < 1`, and `(1-t) R(0) <= R(2)`, or in
  energy form `L (R(0)-R(2)) <= delta R(0)`.
- Conclusion: `(1-delta)^k R(2u) <= R(4u)`.
- `delta = 1/2` recovers `macro_ratio_of_block_energy`, since `1 - 1/2 = 1/2`.
- From the one-step eps <= c/side, via `R(0)-R(2) <= 2(R(0)-R(1))` and
  `u = side/2`, we get `delta = c/k` and `kappa = (1-c/k)^k`, which tends to
  `e^(-c)`. This matches the odd chain's constant.
- The odd chain's general-k survival is `block_survival_of_oneStep_energy`.
  All constants are rational powers; no exponential is used.

| Declaration | Source | Role |
| --- | --- | --- |
| `block_bernoulli_pow`, `floor_of_block_energy` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSmoothedTrajectory.lean:153,166` | Bernoulli block bound; relative energy to floor. |
| `macro_ratio_of_twoStep_block_general`, `..._energy_general` | `:211,228` | Even compiler with free delta. |
| `block_survival_of_oneStep_energy` | `:240` | `((1-delta)^k)^i R(0) <= R(s i)`. |
| `NomeSchedule`, `dyadicNomeSchedule`, `NomeScheduleAFJustified` | `:266,285,303` | Abstract schedule; interface witness; **OPEN** AF Prop. |
| `trajRadius`, `trajWidth`, `trajWidth_gt_side`, `trajWidth_ratio`, `side_split` | `:307,310,312,318,322` | Explicit radius/width; dyadic split. |
| `DyadicSmoothedTrajectory` (+ `radius`, `familyVector`, `state`, `response`, `familyNorm`, `MacroRatioAt`) | `:329-370` | Trajectory data and per-scale objects. |
| `PathEpsBound`, `PathFamilyRadiusSurvival` | `:381,386` | **OPEN** H1, H2. |
| `PathNonDegradingFloor`, `PathVarianceMassFloor` | `:392,398` | **OPEN** alternative H2'; scalar link. |
| `blockEnergy_of_pathEps`, `path_macroRatio` | `:405,425` | H1 to block energy; H1 to uniform macro ratio. |
| `path_macro_conclusion`, `path_macro_conclusion_absolute` | `:442,478` | **Main conditional theorem**; absolute variant. |
| `pathNonDegradingFloor_of_familyRadiusSurvival` | `:509` | H2 + scalar condition gives H2'. |
| `path_rate_screen` | `:527` | Necessary screen hidden in H1. |
| `PathUnitRatioBridge`, `path_unit_anchor_floor` | `:554,564` | **OPEN** bridge; feeds the line-132 unit consumer. |
| `dyadicPhysicalSpacing`, `dyadicSpacingToZero`, `trajectoryDynamicFamily`, `PathCubeContraction`, `nomeSchedule_eventually_not_le_half` | `:583-613` | B04l interface; **OPEN** contraction Prop; w>1/2 screen. |

## Verification boundary

Each Lean run went through `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 8 --check`. A wrapper refused to start while any
other Lean/lake/safe_lean_build process existed. A 10 s memory sampler was
set to abort on memory-pressure level >= 2 or available RAM < 8 GiB.

Accepted final run: exit 0, with no error, warning or sorry. There are 26
`#print axioms` gates:

- 23 report `[propext, Quot.sound]`;
- 2 report `[propext]` (`DyadicSmoothedTrajectory`,
  `nomeSchedule_eventually_not_le_half`);
- 1 reports no axioms (`NomeSchedule`).

The olean was emitted to
`lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSmoothedTrajectory.olean`.
Peak load1 14.04, peak pressure level 1 (normal), minimum available RAM
22764 MiB, swap 0. Logs (Mac, outside repo):
`~/ymlean_prover_scratch/logs/check-p6final-20261005-201011.out` (SHA256
`72288aae66ebc373ae6b0dc83d1395e13c18c5b67207a5623ce06f25c57c8ca3`) and
`~/ymlean_prover_scratch/logs/mem-p6final-20261005-201011.log`.

Final source SHA256 (`BF4WilsonAllNomeDyadicSmoothedTrajectory.lean`):
`4e9168b7f1807624fbeeee59c9312d6a21050adb44b2747028a987ea6ba8b35a`.

Earlier scratch runs are not evidence for this source:

- p6a passed, with two unused-variable warnings; those hypotheses were then
  removed;
- p6b passed before the axiom prints for two defs were added.

`scripts/lean_forbidden_token_scan.py` reported 0 executable hits. The import
is registered in `lean/YMGap.lean`, but registration is not root
verification. No full/root build, full audit, guard, broad metrics run or CI
was used. The commit adds no new sorry, axiom, classical shortcut,
noncomputable declaration, frontier change or replacement carrier.
