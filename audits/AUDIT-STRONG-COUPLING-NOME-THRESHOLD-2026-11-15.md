# AUDIT — StrongCouplingNomeThreshold (2026-11-15)


File: `lean/YMGap/RG/StrongCouplingNomeThreshold.lean`. Label: **PROVED threshold plus PROVED no-go (V3) for this method. NOT gap evidence. No chart closure and no mass-gap claim.**

U(1) note: everything here is abelian-valid strong-coupling work, so it is not non-abelian evidence. Every theorem docstring carries this note.

## Where `w = 1/1024` enters (step 1)
- `existingNome_allNome_strongCoupling` (`BF4WilsonAllNomeStrongCouplingUniformRate.lean:453`) instantiates the already-general `allNome_strongCoupling_vacuumSq_all_widths` (:443).
- `w` enters only through three guard hypotheses, discharged at 1/1024 by `existingNome_guards` (`BF4ExactSlabSmallNomeHaarComparison.lean:195`) and `existingNome_entropyRate` (`BF4ExactSlabSummableCoreRate.lean:37`):
  1. `heatRatio w = 32w³ ≤ 1/2`, which needs `w ≤ 1/4`;
  2. `δ := heatRemainderBound w = 128w³ < 1`, which needs `w < 0.198`;
  3. `entropyRate 625 (adjustedCoreRate w hd) < 1`, where `adjustedCoreRate = pairedRate δ · (1−δ)^(−48)` and `pairedRate δ = 2δ + δ²`.
- The rate is `timeRate = entropyRate 96 (1/384) = 1/4`, a constant independent of `w`. So the rate at any admissible `w` is 1/4, with two-step rate 1/16.
- Threshold function: `T(δ) = 625·(2δ+δ²)·(1−δ)^(−48)` with `δ = 128w³`. Guard 3 is the binding one.

## Results (step 2)
- `guards_of_delta_le` (:92): closed form. `0 ≤ w`, `heatRemainderBound w ≤ δ0 ≤ 1/2`, `δ0 < 1` and `T(δ0) < 1` together give `SCGuards w`. It uses monotonicity of `128w³`, of `pairedRate`, of `recipPos` (antitone) and of `^48`.
- `threshold_inv55` (:133): `T(δ(1/55)) < 1`, by `decide +kernel`. Numerically `T ≈ 0.99826`.
- `scGuards_of_le_inv55` (:138) and `uniformSeedGap_of_le_inv55` (:143): the guards and the width-uniform seed (`UniformSeedGap`, any `budget < timeRate = 1/4`) hold for every `0 < w ≤ 1/55`.
- `uniformSeedGap_inv64` (:149): the largest dyadic point, `w = 1/64`, where `T ≈ 0.625`.
- `timeRate_eq` (:155): `timeRate = 1/4`.

## No-go (step 3, V3)
- `not_scGuards_of_inv54_le` (:160): for every `w ≥ 1/54`, guard 3 fails for every proof `hd`. Since `inverseFaceFloor ≥ 1`, `625·pairedRate(δ(1/54)) ≈ 1.0165 ≥ 1` already.
- `not_scGuards_dyadic` (:184): 1/32, 1/16, 1/8, 1/4 and 1/2 are all unreachable.
- `remainder_ge_one_quarter_half` (:194): at `w = 1/4` (δ = 2) and `w = 1/2` (δ = 16), guard 2 itself fails, independent of the entropy count.
- Bottleneck constant: the core-count entropy degree **625** multiplying the paired heat rate `2·128·w³`. This needs roughly `160000·w³ < 1`. The collar factor `(1−δ)^(−48)` costs only about 4% near the threshold.
- The true threshold of `T` is `w* ≈ 0.01819` (between 1/55 and 1/54). That is a factor of about 27.5 below 1/2. Even with the 625 removed, guards 1 and 2 cap the method at `w < 0.198`, so 1/2 is unreachable in principle.
- This is a limit of this method's constants, not a statement about the true contraction at larger `w`.

## Verification
- Box only. Nothing was run on the Mac.
- Compiled by a direct `lean -s 65536 -M 6144` call (`LEAN_NUM_THREADS=2`), not by lake. The call used the overlay `LEAN_PATH` (`/workspace/v3logs/overlay`): the box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`, output hash `738aabd667d00f10`. That module is not buildable on the box; see `AUDIT-MIXRATE-SEED-WIDTH-NOGO-2026-11-15.md`.
- Compiles:

| Attempt | Result | Peak RSS | Min free RAM | Notes |
|---|---|---|---|---|
| 1 | rc 1 | 1,677 MiB | 12,301 MiB | unknown identifier `HKPos`; one `decide` hit maxRecDepth |
| 2 | rc 1 | 1,685 MiB | 12,352 MiB | `Q'.mul_one` name |
| 3 | rc 0 | 1,696 MiB | 12,235 MiB | |
| final (docstrings) | rc 0, zero warnings | 1,701 MiB | 12,363 MiB | |

- The decides are cheap: plain `decide` on small rationals, plus `decide +kernel` for `T(δ(1/55)) < 1` and `1 ≤ 1^48`. Whole-file compile time is about 1.5 s.
- No `sorry`/`admit`/`Classical`/`native_decide`/`omega`/`simpa`/Mathlib.
- Axioms (temp-file `#print axioms`, file deleted afterwards):
```
'YMGap.RG.StrongCouplingNomeThreshold.SCGuards' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.threshold' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.uniformRate_of_guards' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.uniformSeedGap_of_guards' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.guards_of_delta_le' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.inv55' does not depend on any axioms
'YMGap.RG.StrongCouplingNomeThreshold.inv54' does not depend on any axioms
'YMGap.RG.StrongCouplingNomeThreshold.threshold_inv55' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.scGuards_of_le_inv55' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.uniformSeedGap_of_le_inv55' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.uniformSeedGap_inv64' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.timeRate_eq' does not depend on any axioms
'YMGap.RG.StrongCouplingNomeThreshold.not_scGuards_of_inv54_le' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.not_scGuards_dyadic' depends on axioms: [propext, Quot.sound]
'YMGap.RG.StrongCouplingNomeThreshold.remainder_ge_one_quarter_half' does not depend on any axioms
```

## Addendum: could the 625 be improved? (ANALYSIS, not a theorem)
- **Where 625 comes from.** `ClusterCount4DProgress.lean:44,300` gives `K = (D+1)² = 625` with `D = 24`, the degree of the Z⁴ plaquette adjacency graph (`z4Chain`). That is the tour-plus-mask lattice-animal code of `BddLatticeAnimal`. It is used as the per-size count rate `625^n` in `BF4ExactSlabActiveCoreCount.lean:6,104`, and so enters `entropyRate 625` in the guard.
- **Room to improve.** The tour code is crude. The standard Klarner/Kesten bound is about `e·D ≈ 65`, and the true plaquette-animal growth constant is smaller still. Sharper polymer counting is plausible but is not formalized here.
- **Reachable `w` if the constant were K** (numerical solution of `K·(2δ+δ²)·(1−δ)^(−48) = 1`, `δ = 128w³`, with the actual guard expressions):

| K | best w | about |
|---|---|---|
| 625 | 0.01819 | 1/55, proved |
| 65 | 0.0357 | 1/28 |
| 25 | 0.0447 | 1/22 |
| 1 | 0.0718 | 1/14 |

- **Analysis, checked against the guard definitions:**
  - Even with `K = 1`, the binding factor is `pairedRate δ = 2δ+δ²` together with the collar factor `(1−δ)^(−48)`. The 48 comes from `adjustedCoreRate = pairedHeatRate · inverseFaceFloor^48`.
  - Guard 2, `heatRemainderBound w = 128w³ < 1`, gives `w < (1/128)^(1/3) ≈ 0.198`.
  - Guard 1, `heatRatio w = 32w³ ≤ 1/2`, gives `w ≤ 1/4`.
  - These two only bind after the entropy and collar factors are gone. So improving the counting constant alone cannot pass `w ≈ 0.072`, and `w = 1/2` is out of reach for this whole guard structure.
- The proved statement remains `not_scGuards_of_inv54_le`, with `K = 625`.
