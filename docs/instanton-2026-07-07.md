# The instanton / semiclassical mechanism — does the dilute-gas GENERATE the gap, or is the large-instanton IR = singleStep?

**Deliverable Lean file:** `lean/YMGap/Continuum/InstantonDiluteGas.lean` (wired into `YMGap.lean`).
Full `lake build` **green = 735 jobs** (+1 file); `YMGapGuard` **frontier-guard OK = 5** Clay-frontier
types unconditionally uninhabited (UNCHANGED — nothing new inhabited). All 14 gated load-bearing
declarations `#print axioms ⊆ {∅, [propext], [propext, Quot.sound]}` (`su2_density_value`,
`su2_density_IR_divergent` are axiom-FREE); no `sorry`/`sorryAx`, no `native_decide`, no
`Classical.*`, no `ring`. MAIN tree, NEW file, Lean-core only (`Q'`/`Nat` + `finSum`/geometric-tail
+ the proved `condensateCReal`). **Committed: nothing** (per instruction).

---

## 0. HEADLINE VERDICT (machine-checked, maximally adversarial)

**The BPST instanton action `S_inst = 8π²/g²` gives the essential singularity `exp(−8π²/g²)`, which
is CONSTRUCTIBLE as a CReal in `[0,1]` (its positivity is the RED HERRING, free). But the 't Hooft
instanton DENSITY `d(ρ) ~ ρ^{(11N/3)−5}` is IR-DIVERGENT at large instanton size — for SU(2),
`ρ^{7/3}` with power `7/3 > 0` (PROVED, decide) — and this divergence is UNIVERSAL for every pure
SU(N) with `N ≥ 2` (PROVED, omega). The SMALL-instanton contribution is convergent/constructible (a
uniform geometric budget, PROVED); the LARGE-instanton size integral has NO finite budget (PROVED,
Archimedean). So the dilute-instanton-gas does NOT generate the mass constructively: it CONFIRMS the
essential singularity but ISOLATES the large-instanton IR = the confinement scale = the
non-perturbative measure = `singleStep`. This is a further confirmation of the SAME irreducible core
in semiclassical form, PLUS a genuinely new machine-checked IR-divergent-density theorem. No guarded
frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.**

The task's most adversarial branch is **CONFIRMED**: the small-instanton is convergent but ≠ the mass;
the large-instanton IR = `singleStep`.

---

## 1. THE INSTANTON ACTION + ESSENTIAL SINGULARITY (task point 1) — CONSTRUCTIBLE

- `S_inst = 8π²/g²` (BPST instanton, exact). Instanton-induced effects `~ exp(−S_inst) = exp(−8π²/g²)`
  = the essential singularity (all Taylor coefficients vanish at `g²=0`, invisible to perturbation
  theory, yet strictly positive).
- **`instantonAmplitude k := condensateCReal k`** — the essential singularity as a genuine CReal
  (same `exp(−const/g²)` functional form as the condensate; with the running coupling
  `8π²/g²(ρ) = β₀ log(1/ρΛ)` it is geometric in the block index). `instantonAmplitude_nonneg`
  (`≥ 0`, TRIVIAL — the red herring) and `instantonAmplitude_le_one` (`≤ 1`) PROVED.
- **`betaZeroCoeff N = 11N/3`** exact `Q'`; `betaZeroCoeff_pos` (`β₀ > 0`, `N ≥ 1`, asymptotic freedom).

## 2. THE INSTANTON DENSITY + THE LARGE-INSTANTON IR (task point 2) — the crux, PROVED

The 't Hooft one-instanton density over the size collective coordinate `ρ`:

    d(ρ) dρ ~ (1/ρ⁵)·(8π²/g²(ρ))^{2N}·exp(−8π²/g²(ρ)) dρ.

With `exp(−β₀ log(1/ρΛ)) = (ρΛ)^{β₀}` (running coupling), up to the `(8π²/g²)^{2N}` log correction:

    d(ρ) dρ ~ ρ^{(11N/3)−5} dρ,   β₀ = 11N/3.

- **`densityExponent N = 11N/3 − 5`** exact `Q'`.
- **SU(2) (`N=2`): `densityExponent 2 = 7/3`** (`su2_density_value`, axiom-free `decide`;
  `22/3 − 5 = 7/3`, sympy-exact).
- **`su2_density_IR_divergent : 0 < densityExponent 2`** (axiom-free `decide`): `d(ρ) ~ ρ^{7/3}` GROWS
  at large `ρ`, so `∫^∞ d(ρ) dρ` DIVERGES — the large-instanton / IR problem: the dilute-gas breaks
  down (the large instantons overlap and fill space).
- **`density_IR_divergent (N) (hN : 2 ≤ N) : 0 < densityExponent N`** (omega): the large-instanton IR
  divergence is UNIVERSAL for every pure SU(N), `N ≥ 2` — not an SU(2) accident. (`∫^∞ ρ^p dρ`
  diverges iff `p ≥ −1`; here `p = 11N/3−5 ≥ 7/3`. Verified: SU(3)=6, SU(4)=29/3, SU(5)=40/3, all >0;
  crossover `p=−1` at `N=12/11 ≈ 1.09`, below every integer `N ≥ 2`.)

## 3. THE DECISIVE CHECK (task point 3) — small-instanton convergent vs large-instanton IR

- **SMALL-instanton (`ρ → 0`, integrable): CONVERGENT/CONSTRUCTIBLE.** `ρ^{7/3} → 0`, so
  `∫_0^{Λ⁻¹} d(ρ) dρ` converges. **`smallInst_convergent (N) : finSum smallInstTerm N ≤ condSum`**
  (PROVED via the proved `geometric_tail_closure`) — every partial sum is uniformly bounded by the
  closed geometric budget `condSum = K'/(1−r') = (1/100)/(2/5) = 1/40`.
- **LARGE-instanton (`ρ > Λ⁻¹`): NO FINITE BUDGET = IR DIVERGENCE.** For `ρ ≥ 1` and `p = 7/3 > 0`,
  `ρ^{7/3} ≥ 1`, so the integrand does NOT decay. `largeInstPartialSum_eqv : finSum largeInstTerm N ≃
  ofNat N` (grows linearly), and **`largeInst_no_finite_budget (B) : ∃ N, B < finSum largeInstTerm N`**
  (PROVED, Archimedean via `exists_ofNat_gt` / `Int.self_le_toNat`): the large-instanton size integral
  EXCEEDS ANY finite bound. The dilute-gas has no convergent measure at large instanton size.

So: the instanton ACTION gives the essential singularity (constructible, positivity free); the SMALL
instanton is convergent (constructible); but the mass needs the IR-complete density, and the LARGE
instanton has no finite measure — the large instantons = the confinement = the non-perturbative
measure = `singleStep`.

## 4. THE ISOLATION (task point 4)

`def InstantonLargeSizeIR : Type := SingleStepDefectReduction.SingleStepDefectBound`
(`instantonLargeSizeIR_eq`, `rfl`, Rule 9.8) — UNINHABITED, NOT one of the 5 guarded frontier types.
A dilute-gas mass built with an ASSUMED IR-complete (large-instanton) density would be the Rule-9
fake — deliberately not written.

## 5. HONEST accounting (refuse dodges)

| object | status | evidence |
|---|---|---|
| instanton action `S_inst = 8π²/g²` + essential singularity `exp(−8π²/g²)` as CReal in `[0,1]` | **CONSTRUCTED** | `instantonAmplitude`, `_nonneg`/`_le_one` |
| `exp(−8π²/g²) > 0` positivity | **TRIVIAL — red herring** | free `expNeg` nonnegativity |
| `β₀ = 11N/3 > 0` (asymptotic freedom) | **PROVED** | `betaZeroCoeff_pos` |
| density power `densityExponent N = 11N/3 − 5`; SU(2) = `7/3` | **PROVED (axiom-free)** | `su2_density_value` |
| large-instanton IR divergence `0 < 7/3` (SU(2)) | **PROVED (axiom-free)** | `su2_density_IR_divergent` |
| IR divergence universal `∀ N ≥ 2` | **PROVED** | `density_IR_divergent` |
| small-instanton integral bounded (convergent) | **PROVED** | `smallInst_convergent` |
| large-instanton integral has no finite budget (IR-divergent) | **PROVED** | `largeInst_no_finite_budget` |
| real mass needs the IR-complete large-instanton density | **OPEN = `singleStep`** | `InstantonLargeSizeIR = SingleStepDefectBound` (uninhabited) |

No STOP/cascade condition tripped: the module inhabits none of the 5 guarded frontier types and
produces no unconditional inhabitant of `SingleStepDefectBound` or any guarded bundle. Guard stays at
5. `instanton_verdict : InstantonVerdict` is inhabited by PROVED facts only (essential-singularity
CReal + IR-divergent density + convergent-small + divergent-large) — NOT a frontier type.

## 6. `#print axioms` (all 14 gated decls ⊆ {∅, [propext], [propext, Quot.sound]})

```
pos_of_num_pos                : [propext]
lt_of_lt_of_le                : [propext]
instantonAmplitude_nonneg     : [propext, Quot.sound]
instantonAmplitude_le_one     : [propext, Quot.sound]
betaZeroCoeff_pos             : [propext, Quot.sound]
su2_density_value             : (none)                  ← density power = 7/3, axiom-free
su2_density_IR_divergent      : (none)                  ← 0 < 7/3, axiom-free
density_IR_divergent          : [propext, Quot.sound]   ← universal N ≥ 2
smallInst_convergent          : [propext]               ← small-instanton convergent
largeInstPartialSum_eqv       : [propext, Quot.sound]
exists_ofNat_gt               : [propext, Quot.sound]
largeInst_no_finite_budget    : [propext, Quot.sound]   ← large-instanton IR divergence
instantonLargeSizeIR_eq       : [propext, Quot.sound]   ← isolation = singleStep
instanton_verdict             : [propext, Quot.sound]
```

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (735 jobs).
```

## 7. HONEST FINAL VERDICT — does the instanton generate the gap, or isolate the large-instanton IR?

**It ISOLATES the large-instanton IR = `singleStep`.** The BPST action `S_inst = 8π²/g²` gives the
essential singularity `exp(−8π²/g²)`, which is CONSTRUCTIBLE as a CReal (positivity trivial = the red
herring). The 't Hooft density is IR-DIVERGENT (`ρ^{7/3}` for SU(2), universal for `N ≥ 2`, PROVED).
The small-instanton contribution is convergent (constructible); the large-instanton contribution has
no finite measure (IR-divergent) — the large instantons overlap = the confinement scale = the
non-perturbative measure = `InstantonLargeSizeIR = SingleStepDefectBound.singleStep` (UNINHABITED).
So the dilute-instanton-gas does NOT generate the mass constructively: the essential singularity is
constructible, the small-instanton is convergent, but the MASS needs the IR-complete large-instanton
density = `singleStep` (the renormalon). This is a further confirmation of the SAME irreducible core
in semiclassical form. **The genuinely new machine-checked pieces** are (i) the exact IR-divergent
density power `densityExponent N = 11N/3 − 5` with the axiom-free SU(2) value `7/3` and its
positivity, and its universality for all `N ≥ 2`; and (ii) the convergent-small / no-finite-budget-
large split (`smallInst_convergent` vs `largeInst_no_finite_budget`). No guarded frontier bundle is
inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN. The next attack is unchanged:
the spacing-uniform gap survival `singleStep` = the IR-complete large-instanton / interacting measure.
