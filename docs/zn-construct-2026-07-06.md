# Constructing z_n from the REAL WilsonProbFunctional — verdict + exact gap

**Deliverable Lean file:** `lean/YMGap/Continuum/ZnWilsonConstruction.lean` (wired into
`YMGap.lean`; full `lake build` green = **711 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited). Numerics verified (mpmath dps 50, sympy exact).
**Commits: none** (per instruction).

---

## 0. The obligation

CONSTRUCT the interacting connected amplitude `z_n = ∫ e^{−S_int} χ dHaar / Z` from the library's
REAL Wilson probability functional, rather than merely BOUND it. In
`ContinuumFieldMeasure.InteractingContinuumMeasure`, `z_n` (`zAmp`) is a machine-checked FREE field
(`interacting_zAmp_free_dodge`: the whole structure is inhabited by `zAmp ≡ 0`). The decisive
question: is `WilsonProbFunctional` a GENUINE constructed measure that CONSTRUCTS `z_n`, or an
abstract/free positive-functional interface that still carries `z_n` as free data?

---

## 1. HEADLINE VERDICT (machine-checked, axiom-clean)

**`WilsonProbFunctional` is a GENUINE CONSTRUCTED positive functional — NOT a free field —
and it CONSTRUCTS `z_n` AT FIXED SPACING, removing the free-field underdetermination there.
It does NOT construct the INTERACTING CONTINUUM `z_n`.** The exact remaining foundational gap is
the interacting, plaquette-coupled block-spin RG weight and its `a→0` limit — the named residual
already carried by `WilsonRGTower` / `InteractingContinuumMeasure.uniformWickTreeDom`.

Nothing closes. No guarded frontier bundle is inhabited. The free-field dodge is refused. The 4D
Yang–Mills mass gap remains **OPEN**.

---

## 2. Is `WilsonProbFunctional` genuine or abstract/free?  GENUINE — read the definitions

This is the adversarial core of the task. Verdict from reading the actual code:

- **`WilsonFunctional.wilsonCharExp t ht s = dim(s)·e^{−t·C₂(s)}`** is a **CONCRETE `CReal`** — the
  heat-kernel character moment `⟨χ_s⟩_t`, built from the A1 transcendental exponential
  `ExpNeg.expNeg` and the SU(2) Casimir `C₂(s) = s(s+2)/4`. This is an ACTUAL computed value, not a
  slot. `wilsonCharExp_nonneg` (`≥ 0`) and `wilsonCharExp_unit` (`⟨χ₀⟩ = 1`, normalization) are real
  theorems about it.
- **`WilsonProbFunctional.wilsonE`** is the genuine positive normalized expectation on a real
  observable *-algebra (`wilsonEdgeAlg`: Clebsch–Gordan fusion `mul`, `χ₀` unit, `id` star). Its
  value on a character combination is the genuine linear moment `Σ_i c_i ⟨χ_i⟩_t`; on the GNS
  diagonal it is `WilsonFunctional.coneExp` (the character-Gram energy). It is a real
  `ProbFunctionalC` whose GNS positivity is either UNCONDITIONAL on the nonnegative-coefficient cone
  (`wilsonConeProbFunctionalC`, `coneExp_nonneg`) or discharged from ONE named all-order Gram-PSD
  input (`wilsonProbFunctionalC` ← `MomentSquarePos`).

So `WilsonProbFunctional` is **NOT** an abstract functional carrying `z_n` as free data at fixed
spacing: the character-basis amplitude is a genuinely constructed transcendental value.

**Machine-checked connection (new file):**

| declaration | content | axioms |
|---|---|---|
| `zWilson t ht n := wilsonCharExp t ht n` | `z_n` CONSTRUCTED as the Wilson-functional expectation `⟨χ_n⟩_t` — a concrete `CReal` | (def) |
| `zWilson_nonneg` | the constructed amplitude is `≥ 0` | `propext, Quot.sound` |
| `zWilson_unit_pos` | `zWilson … 0 = ⟨χ₀⟩_t ≥ 1` — nonzero, carries content the free dodge (`zAmp ≡ 0`) drops | `propext, Quot.sound` |
| `zWilson_is_functional_expectation` | `wilsonE t ht wOne ≃ zWilson t ht 0` — it IS the real *-algebra functional's value on `χ₀` | `propext, Quot.sound` |
| `zWilson_functional_normalized_le` | `wilsonE t ht wOne ≤ 1` — pins `⟨χ₀⟩ = 1` (a genuine state) | `propext, Quot.sound` |

The free-field underdetermination is **removed at fixed spacing**: `z_n^fixed` is a constructed,
positive, normalized heat-kernel expectation — the already-proved strong-coupling gap amplitude.

---

## 3. THE DECISIVE CHECK — does this construct the CONTINUUM `z_n`?  **NO** (two independent proofs)

The Wilson functional constructs the FIXED-SPACING amplitude; the CONTINUUM (`a→0`) interacting
`z_n` is a genuinely different object, and the Wilson character/heat-kernel functional PROVABLY
FAILS to be it:

**(1) The character/heat-kernel expansion DIVERGES at the continuum.** New theorem
`zWilson_charbasis_diverges_continuum` (re-exporting `ZnCharacterSumFrontier.
charRate_exceeds_one_at_continuum`, kernel-`decide`, **axiom-free**): the per-plaquette character
rate `ρ = coeffW w 1 = 2w³` exceeds `1` at `w = 9/10` (`= 729/500 = 1.458 > 1`). The crossover
`2w³ = 1` sits at `w* = (1/2)^{1/3} = 0.79370…`, so the ENTIRE asymptotically-free / continuum window
`w ∈ (0.794, 1)` — where every `a→0` scale lives — is OUTSIDE convergence. `zWilson` does not
converge to a continuum amplitude: **wrong basis for `a→0`.** (`zWilson_charbasis_overshoots_continuum`:
it also overshoots the field activity `g² = 1−w` by a factor `14.58`.)

**(2) The RG inverse limit whose Kolmogorov consistency is PROVED is the FREE product measure — its
interacting connected amplitude VANISHES.** New theorem `zWilson_free_continuum_no_interaction`
(re-exporting `ContinuumFieldMeasure.freeContinuum_no_interaction`). Reading the machinery:
`WilsonConsistency.wilsonConsistency` and `WilsonRGTower.wilsonTowerConsistency` DO prove Kolmogorov
consistency and DO assemble the genuine inverse-limit Wilson measure `μ_∞`
(`wilsonContinuumMeasure`, `wilsonTowerContinuumMeasure`, with the Daniell–Kolmogorov projection law
`π_k(μ_∞) = μ_k` proved) — **but for the INDEPENDENT-PRODUCT heat-kernel weight**
`∏_i dim(s_i)·w^{C₄(s_i)}`, explicitly **NOT** the plaquette-COUPLED interacting Wilson Boltzmann
weight (documented verbatim in both files' headers: *"IT IS NOT the interacting, plaquette-COUPLED
Wilson Boltzmann weight … the interacting weight and its block-spin RG flow … are the precise
residual"*). The free product's connected two-point vanishes identically
(`FieldMeasureUrsell.freeConnected2_eq_zero`): the constructed continuum amplitude is
`z_n^free = 0` — the Gaussian free field.

Hence the REAL Wilson functional constructs exactly two things: the **fixed-spacing interacting
amplitude** (positive, the proved gap) and the **continuum FREE amplitude** (which vanishes). It
does NOT construct the **interacting continuum `z_n`**.

---

## 4. Foundational status of the other pieces (exhaustive, adversarial)

- **`ContinuumMeasure.InvLim`** — the inverse (projective) limit IS a genuine constructive `Σ`-type
  (consistent threads), MLTT/HoTT-valid, with the projection/pushforward laws proved (`rfl`). BUT
  the per-scale carrier `M_k = Prob(SU(2)^{E_k})` is **abstract** (`M : Nat → Type` left as a free
  parameter) and the Kolmogorov consistency `is_consistent` is an **input hypothesis**. The header
  states plainly: it does NOT construct the `M_k`, does NOT perform the Daniell–Kolmogorov
  σ-additive extension — *"the open analytic content … the Clay existence problem."* So
  `ContinuumMeasure` is a genuine inverse-limit STRUCTURE but the a→0 measure is carried as free
  data (except when instantiated by the FREE-product tower, §3(2)).
- **`ContinuumExistence`** — S3 `finiteVolumeExpectation` genuinely constructs the interacting
  reweighted expectation `E_Λ(o) = Ew_Λ(o)·recip(Z_Λ)`, and S5 `infiniteVolumeExpectation`
  genuinely constructs a `CReal` inverse limit with modulus — BUT this is the **thermodynamic**
  (`Λ→∞`) limit at **FIXED spacing**, from a weak-coupling KP increment datum
  (`KPIncrement.KPIncrementData`, a genuine smallness HYPOTHESIS), and S6 positivity is conditional
  on the full-Wilson-PSD (OS2). It is not the `a→0` scaling limit.
- **`InteractingContinuumMeasure`** — `zAmp` is Q'-valued (a rational placeholder), while the
  genuine Wilson amplitude is an irrational `CReal` (`dim·e^{−tC₂}`): the structure's amplitude
  field cannot even faithfully HOLD the real heat-kernel value — an additional honest indicator that
  its `zAmp` is a free surrogate, not the constructed object.

---

## 5. Cascade / STOP audit (mandatory)

**No STOP condition tripped. No guarded bundle inhabited. No cascade triggered.**

- `ZnWilsonConstruction.lean` produces theorems ABOUT the constructed fixed-spacing amplitude and its
  continuum failure. It does **NOT** inhabit `InteractingContinuumMeasure`, `IsserlisPenroseData.
  pertRep`, `KPAmplitude`, `SinglePolymerActivity`, or any of the 5 guarded Clay-frontier types
  (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`). Full
  build: `frontier-guard OK: 5 … unconditionally uninhabited`, 711 jobs (710 → 711 = the +1 module).
- The free-field dodge is **refused**: the constructed amplitude is nonzero (`zWilson_unit_pos`,
  `⟨χ₀⟩ ≥ 1`), unlike the dodge's `zAmp ≡ 0`.
- **`#print axioms`** for all 7 load-bearing decls: `[propext, Quot.sound]` (four) or **no axioms**
  (the two kernel-`decide` continuum-divergence facts) or `[propext]` (the free-connected fact). No
  `Classical.*`, no `sorryAx`, no `native_decide`, no `sorry`/`admit` (banned tokens appear only in
  docstring prose).

---

## 6. Numeric validation (mpmath dps 50, sympy exact)

- Normalization `wilsonCharExp(t, 0) = 1·e^{−t·0} = 1` for `t ∈ {0, 1/2, 1, 10}` — exact `1.0`.
- `coeffW(9/10, 1) = 2·(9/10)³ = 729/500 = 1.458 > 1` (sympy exact) — the decisive divergence.
- Field-activity overshoot: `1 − 9/10 = 1/10 < 1.458`, factor `14.58`.
- Crossover `2w³ = 1` at `w* = (1/2)^{1/3} = 0.79370052598…`; `2·(79/100)³ = 0.986 < 1 < 1.024 =
  2·(8/10)³`.
- Fundamental moment nonzero: `wilsonCharExp(1/2, 1) = 2·e^{−3/8} = 1.37457855758…`,
  `wilsonCharExp(1, 1) = 2·e^{−3/4} = 0.94473310548…` (both `> 0`, carrying content).

---

## 7. HONEST FINAL VERDICT

The library's `WilsonProbFunctional` is a **GENUINE CONSTRUCTED positive normalized functional**
(concrete transcendental heat-kernel character moments), and it **CONSTRUCTS `z_n` at FIXED SPACING**
— removing the free-field underdetermination there (the constructed amplitude is positive,
normalized, and provably not the `zAmp ≡ 0` dodge). This is real, machine-checked progress on
locating the frontier: the free-field dodge is defeated **at fixed spacing** by the real functional.

But the functional does **NOT** construct the **INTERACTING CONTINUUM `z_n`**, for two independent
machine-checked reasons: (1) the character/heat-kernel basis provably **diverges** across the entire
`a→0` window (`2w³ > 1`); (2) the RG inverse limit whose Kolmogorov consistency is actually PROVED
is the **FREE product** measure, whose interacting connected amplitude **vanishes** (Gaussian free
field). The exact remaining foundational gap is the **interacting, plaquette-coupled block-spin RG
weight and its `a→0` limit** — the config-space Gaussian integral of `e^{−S_int}`, i.e. the named
residual of `WilsonRGTower` and the content of `InteractingContinuumMeasure.uniformWickTreeDom`
(equivalently `IsserlisPenroseData.pertRep`).

**No guarded frontier bundle is inhabited; nothing is faked; the free-field dodge is refused; the
4D Yang–Mills mass gap remains OPEN.** `z_n` is constructed at fixed spacing from the real Wilson
functional; the interacting continuum `z_n` is the free interacting-integral frontier — located
exactly, not closed.

---

## 8. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (711 jobs).
```

`ZnWilsonConstruction.lean`, 7 load-bearing decls, `#print axioms ∈ {[], [propext],
[propext, Quot.sound]}`. Lean-core only (`Q'`/`CReal`, reused PROVED `wilsonCharExp`, `wilsonE`,
`wilsonE_one_equiv`, `charRate_exceeds_one_at_continuum`, `freeContinuum_no_interaction`); no
Mathlib, no `ring`, no `native_decide`. All witnesses `Type`-level.
