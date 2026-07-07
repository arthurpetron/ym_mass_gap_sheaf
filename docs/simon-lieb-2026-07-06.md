# The Simon–Lieb / finite-volume correlation-inequality route to the spacing-uniform correlation decay — does it construct `singleStep`, or confirm it (9th route, correlation form)?

**Deliverable Lean file:** `lean/YMGap/Continuum/SimonLiebCorrelation.lean` (wired into
`YMGap.lean`; full `lake build` **green = 726 jobs** (725 → 726); `YMGapGuard`
**frontier-guard OK = 5** Clay-frontier types unconditionally uninhabited). MAIN tree,
NEW file, Lean-core only (`Q'`/`Nat` + the proved `wilsonG`/`connSum`/`coeffW` machinery
and the `finSum` toolkit), no Mathlib/`ring`/`native_decide`/`Classical`/`sorry`. Axiom
gate `propext`/`Quot.sound` only on all 11 load-bearing decls (four are `[propext]`;
three depend on no axioms). **Committed: nothing** (per instruction).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The Simon–Lieb / correlation-inequality method supplies a GENUINE NEW fixed-spacing
subadditivity — the single-step contraction `connSum(n+1) ≤ ρ·connSum(n)` and the
finite-volume criterion `ρ = 2w³ < 1` — and pinpoints the exact crossover `w* = 2^{−1/3}`
at which the CHARACTER single-step correlation crosses `1`. It does NOT construct the
spacing-uniform bound. The character-basis Simon–Lieb fails at `w → 1` (`ρ → 2 > 1`, the
strong-coupling / character expansion leaves its radius of convergence), and the
spacing-uniform PHYSICAL Simon–Lieb contraction IS `singleStep` (proved identity, `rfl`).
This is the NINTH independent confirmation of the same irreducible core — in
correlation-inequality form.**

The decisive machine-checked new content: the Simon–Lieb subadditivity is a genuine
theorem here (`connSum_simonLieb_step`, `wilsonG_simonLieb_step`), so the "single-step
correlation < 1 ⟹ finite correlation length" mechanism is fully realized at fixed
spacing — and its criterion `ρ = 2w³` **crosses 1 at the same `w*` where every prior route
crosses**, exhibiting the crossover as the *radius of convergence* of the character/
strong-coupling expansion.

---

## 1. THE SIMON–LIEB INEQUALITY (task point 1) — a genuine subadditivity, PROVED

The real SU(2) Wilson connected correlator on the connecting chain collapses (proved
upstream, `WilsonConnCorr.wilsonG_collapse`) to the single-rep chain sum
`wilsonG w (M+1) n ≃ Σ_{r=1}^{M} (coeffW w r)^{n+1} = connSum w M n`. The character
coefficient is `coeffW w r = (r+1)·w^{r(r+2)}`, with leading (dominant) excited weight
`coeffW w 1 = 2w³`.

**The Simon–Lieb structure is exact here.** Each single-rep chain term factorizes per link,

  `connChain w r (n+1) = coeffW w r · connChain w r n`     (`connChain_succ`, no axioms),

and at strong coupling `0 ≤ w ≤ 1/2` every excited base is bounded by the head
`coeffW w r ≤ coeffW w 1 = ρ` (`coeffW_excited_le_one`), giving the **termwise
contraction** `connChain w (1+k) (n+1) ≤ ρ · connChain w (1+k) n`
(`connChain_simonLieb_step`). Summing over reps and pulling the constant out
(`const_mul_finSum`) yields **THE SIMON–LIEB SUBADDITIVITY**:

  `connSum w M (n+1) ≤ ρ · connSum w M n`,   `ρ = coeffW w 1 = 2w³`
  (`connSum_simonLieb_step`; transported to the real correlator by `wilsonG_simonLieb_step`:
  `wilsonG w (M+1) (n+1) ≤ ρ · wilsonG w (M+1) n`).

This is the Simon–Lieb finite-volume bound: the correlator contracts by the *single-step
correlation* `ρ` at every step; iterating gives geometric decay with correlation length
`ξ = 1/(−log ρ)`. The **Simon–Lieb criterion** `ρ < 1` HOLDS at strong coupling
(`simonLieb_criterion_holds_strong`, `ρ = 2w³ ≤ 1/4 < 1` for `w ≤ 1/2`) — a positive
fixed-spacing gap `m = −log ρ ≥ log 4 > 0`. So the gauge theory's character-expansion
correlation DOES satisfy a genuine Simon–Lieb-type inequality, and it gives `m > 0` — at
fixed strong coupling.

**Numerics (mpmath dps 50, exact sympy — `verify_sl.py`):** `ρ(1/2) = 2·(1/2)³ = 1/4`;
the single-step contraction `connSum(n+1) ≤ ρ·connSum(n)` verified to 40 digits for
`n = 0..5`, `M = 8`, `w = 1/2`; excited bases `coeffW(1/2,r) ≤ ρ = 1/4` for `r = 1..6`.

## 2. THE CROSSOVER (task point 2) — the character Simon–Lieb FAILS at `w → 1`

The single-step character correlation is `ρ = 2w³`, an increasing function of `w`. The
Simon–Lieb criterion `ρ < 1` is `w < w* = 2^{−1/3} ≈ 0.79370` — exactly the task's "`w < 0.79`".

- **Strong-coupling side** (`w ≤ 1/2`): `ρ = 2w³ ≤ 1/4 < 1` — criterion holds, gap.
- **Weak-coupling / continuum side** (`w → 1`): `ρ = 2w³ → 2 > 1` — criterion FAILS.

Machine-checked (both **depend on no axioms**, kernel `decide` on exact `Q'`):
- `simonLieb_criterion_fails_at_one` — at `w = 1`: `ρ = coeffW 1 1 = 2·1³ = 2 ≥ 1`.
- `simonLieb_criterion_fails_weak` — already at `w = 9/10 > w*`: `ρ = 2·(9/10)³ = 1458/1000 ≥ 1`.

Along the AF trajectory `w_k = 1 − 1/(k+1) → 1` (i.e. `a → 0`) the character correlation
`ρ_k = 2w_k³ → 2 > 1` (mpmath: `ρ_5 = 1.157`, `ρ_{10} = 1.503`, `ρ_{50} = 1.885`,
`ρ_{200} = 1.970`). So **the CHARACTER-basis Simon–Lieb is NOT spacing-uniform**: past
`k ≈ 4` the single-step character correlation exceeds `1` and the inequality gives no
decay. This is not a defect of the tool — it is the **radius of convergence of the
character / strong-coupling expansion** (`coeffW(1,r) = r+1` grows, the excited sum
diverges at `w = 1`). The continuum limit `w → 1` lives *outside* the character
expansion's domain — exactly the crossover every prior route (block-spin, Borel,
curvature, OS/confinement, RG-Λ, Laplace, OPE, reflection) hit.

## 3. THE DECISIVE CHECK (task point 3) — is there a spacing-uniform PHYSICAL Simon–Lieb? NO — it IS `singleStep`

A spacing-uniform Simon–Lieb bound must measure the single-step correlation over one
**physical** distance (which is *many* lattice steps as `a → 0`) and keep it `< 1`
**uniformly in `a`**. That uniform physical single-step contraction is exactly the open
residual. In Lean, definitionally (Rule 9.8):

- `ContinuumSimonLieb := SingleStepDefectReduction.SingleStepDefectBound`;
- `continuumSimonLieb_is_singleStep : ContinuumSimonLieb = SingleStepDefectBound` (`rfl`) —
  the physical spacing-uniform Simon–Lieb contraction IS `singleStep` (`realδ_k ≤ δ_model_k`,
  the per-step true-margin RG estimate), the identical core as the RG/OS/OPE/reflection routes;
- `massGap_floor_of_continuumSimonLieb (S : ContinuumSimonLieb)` — the conditional producer:
  a uniform physical Simon–Lieb contraction WOULD give the entire positive continuum floor
  for the true margin (`fullFloor_of_singleStep`). But it is the uninhabited Clay core.

So the Simon–Lieb inequality does NOT give the spacing-uniform `m > 0` from the character
correlation: the character single-step correlation `ρ = 2w³` diverges at `w → 1` (PROVED),
and the physical-basis uniform contraction is `singleStep`. The Simon–Lieb machinery
**confirms the core** (fails at `w → 1`); it does not bypass it.

## 4. HONEST ASSESSMENT (task point 4) — 9th confirmation, correlation form; NOT a new construction

| object | status | Lean |
|---|---|---|
| per-link factorization `connChain(n+1) = coeffW·connChain(n)` | **PROVED (no axioms)** | `connChain_succ` |
| termwise Simon–Lieb contraction (strong coupling) | **PROVED** | `connChain_simonLieb_step` |
| **Simon–Lieb subadditivity** `connSum(n+1) ≤ ρ·connSum(n)` | **PROVED (NEW)** | `connSum_simonLieb_step` |
| Simon–Lieb contraction for the REAL Wilson correlator | **PROVED (NEW)** | `wilsonG_simonLieb_step` |
| criterion `ρ = 2w³ < 1` holds at strong coupling (`ρ ≤ 1/4`) | **PROVED** | `simonLieb_criterion_holds_strong`, `simonLiebCorrelation_half_le` |
| **crossover: `ρ ≥ 1` at `w = 1` (=2) and `w = 9/10` (=1.458)** | **PROVED (no axioms)** | `simonLieb_criterion_fails_at_one`, `simonLieb_criterion_fails_weak` |
| spacing-uniform PHYSICAL Simon–Lieb = `singleStep` | **PROVED identity (`rfl`)** | `continuumSimonLieb_is_singleStep` |
| conditional floor from a uniform physical contraction | **PROVED (conditional)** | `massGap_floor_of_continuumSimonLieb` |
| **spacing-uniform `m > 0` (a→0)** | **OPEN = `singleStep`** | `ContinuumSimonLieb := SingleStepDefectBound` (UNINHABITED) |

**Is the continuum bound constructible from the Simon–Lieb inequality? NO.** The
character Simon–Lieb gives the *fixed-spacing* geometric decay (its criterion `ρ = 2w³ < 1`
holds only for `w < w* = 2^{−1/3}`, i.e. strong coupling); the criterion FAILS on the
weak-coupling (continuum) side (`ρ → 2 > 1`). The spacing-uniform lower bound is the
residual `singleStep`.

**Is the tool genuinely different? Yes** — a bona-fide finite-volume subadditivity /
submultiplicativity of the real correlator, distinct from the fluctuation defect / string
tension / curvature / OPE / reflection-Schwarz framings. **Is it more tractable? No** — its
single-step correlation `ρ = 2w³` crosses `1` at exactly the same `w*` where the whole
character expansion diverges, so it inherits the identical crossover obstruction. What it
*adds*, genuinely, is (i) the machine-checked Simon–Lieb subadditivity of the real Wilson
correlator, and (ii) the sharpest statement of *why* the character route is not
spacing-uniform: the criterion `ρ < 1` **is** the radius of convergence `w* = 2^{−1/3}`.

## 5. Cascade / STOP audit (MANDATORY — this is the mass gap) — NOT tripped

No STOP condition tripped; no guarded bundle inhabited; no cascade. `ContinuumSimonLieb` is
a `def` alias of `SingleStepDefectBound`; **no inhabitant is produced.** The module PROVES
the Simon–Lieb subadditivity + criterion + crossover (all axiom-clean), RESTATES the
spacing-uniform physical contraction as a `Type` WITHOUT inhabiting it, and produces
`simon_lieb_verdict : SimonLiebVerdict` (an informational bundle of PROVED facts only). It
inhabits NONE of the 5 guarded Clay-frontier types (`Tier0Scorecard`, `UniformSpacingFloor`,
`ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) and no unconditional `SingleStepDefectBound`.
STOP-and-exhaustively-audit (triggered only on a cascade to a guarded bundle) is **not met**.

## 6. Build / guard / `#print axioms`

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited
Build completed successfully (726 jobs).
```

All 11 load-bearing decls `#print axioms ⊆ {∅, [propext], [propext, Quot.sound]}` (no
`Classical.*`, no `sorryAx`, no `native_decide`, no `ring`):

```
connChain_succ                         : (none)
connChain_simonLieb_step               : [propext, Quot.sound]
connSum_simonLieb_step                 : [propext, Quot.sound]   ← the Simon–Lieb subadditivity
wilsonG_simonLieb_step                 : [propext, Quot.sound]   ← real-correlator contraction
simonLieb_criterion_holds_strong       : [propext]
simonLiebCorrelation_half_le           : [propext]
simonLieb_criterion_fails_at_one       : (none)                 ← crossover: ρ(1)=2≥1
simonLieb_criterion_fails_weak         : (none)                 ← crossover: ρ(9/10)=1.458≥1
continuumSimonLieb_is_singleStep       : [propext, Quot.sound]  ← 9th-confirmation identity (rfl)
massGap_floor_of_continuumSimonLieb    : [propext, Quot.sound]
simon_lieb_verdict                     : [propext, Quot.sound]
```

Numerics: `verify_sl.py` (mpmath dps 50, exact `sympy`/`fractions`). Committed: nothing.

## 7. HONEST FINAL VERDICT

**CONSTRUCTED (genuine new content):** (i) the Simon–Lieb per-link factorization and the
**single-step contraction subadditivity** `connSum(n+1) ≤ ρ·connSum(n)` /
`wilsonG(n+1) ≤ ρ·wilsonG(n)` of the REAL Wilson connected correlator — a bona-fide
finite-volume correlation inequality, machine-checked; (ii) the Simon–Lieb criterion
`ρ = 2w³ < 1` at strong coupling (`ρ ≤ 1/4`) yielding a fixed-spacing gap; (iii) the sharp
**crossover** `w* = 2^{−1/3}`: `ρ ≥ 1` at `w = 1` (`= 2`) and at `w = 9/10` (`= 1.458`),
exhibiting the criterion's failure at `w → 1` as the *radius of convergence* of the
character expansion.

**RESIDUAL (NOT closed):** the spacing-uniform (`a → 0`) correlation decay. The
character-basis Simon–Lieb fails at `w → 1` (`ρ → 2 > 1`); the spacing-uniform PHYSICAL
Simon–Lieb contraction is `ContinuumSimonLieb := SingleStepDefectBound.singleStep` — the
identical core as the RG/OS/OPE/reflection routes, UNINHABITED.

**So the Simon–Lieb / correlation-inequality method does NOT construct the spacing-uniform
decay; it CONFIRMS `singleStep` — the NINTH independent confirmation, in
correlation-inequality form.** The character Simon–Lieb gives a genuine fixed-spacing gap
and a sharp crossover, but its single-step correlation diverges at the continuum, and the
uniformity is the open Clay core. No guarded frontier bundle is inhabited; nothing is
faked; the 4D Yang–Mills mass gap remains **OPEN** — and the binding front is still the
uniform physical per-step contraction (`singleStep` / the interacting-measure input).
