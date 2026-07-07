# The configuration-space su(2) field-measure substrate (`treeDom` / field-Ursell)

**Deliverable.** `lean/YMGap/Continuum/FieldMeasureUrsell.lean` (wired into `YMGap.lean`;
full `lake build` green = **701 jobs**; `YMGapGuard` **frontier-guard OK** = 5 Clay-frontier
types still unconditionally uninhabited; axiom-clean `propext`/`Quot.sound` or empty).
Numerics `fieldmeasure_verify.py` (mpmath dps 50, sympy exact). Commits: none (per instruction).

---

## 0. The obligation

`KPFieldAmplitude.KPAmplitude.treeDom : ∀ k n, zAmp k n ≤ mu^n·(a k)^n` — the field-Ursell
expansion structure — asserts the connected n-cluster amplitude `z_n` over field
configurations **is** the log of the config-space partition function's cluster expansion,
tree-dominated (Penrose) × the single-site activity, so that from `|z_1| ≤ g²` (PROVED,
`ExactSinglePolymerActivity`) the KP amplitude bound `|z_n| ≤ (μg²)^n` follows (PROVED
combinatorially, `KPFieldAmplitude.amplitude_le`). `treeDom` is the config-space **measure**
content the amplitude bound leaves standing. The task: build the minimal constructive
field-measure substrate and report honestly whether `treeDom` is genuinely BUILT or reduced
to a config-space-measure residual.

---

## 1. What is BUILT (finite, genuine, FREE) — `FieldMeasureUrsell.lean`

The **minimal finite-lattice field measure** — the FINITE-LATTICE PRODUCT of the proved
single-mode Gaussians — is constructible in Lean-core and is built here:

| declaration | content | axioms |
|---|---|---|
| `blockSites b = b^4` / `blockSites_two` | the finite `b⁴`-site block lattice (`b=2 ⟹ 16` sites) | none |
| `freeTotalVariance s m = Σ_{x<m} ⟨A_x²⟩` | the FREE product measure's aggregate second moment, a finite sum of the PROVED `gaussSecondMoment s = s²` | — |
| `freeTotalVariance_nonneg` | total variance `≥ 0` (finite sum of proved single-mode variances) | propext |
| **`freeTotalVariance_eq`** | **the finite-product factorisation** `Σ_{x<m} s² ≃ m·s²` (independence ⟹ additive variance) | propext, Quot.sound |
| `freePartition Z1 m = Z1^m` / `freePartition_succ` | the FREE partition function factorises over sites; `log Ξ_free = m·log Z1` additive | none |
| `freePartition_nonneg` | `Ξ_free ≥ 0` | propext |

This is a **genuine** finite product of proved single-mode Gaussians — not a re-labelling.
`gaussSecondMoment s = s·s` is the real single-mode variance `⟨A²⟩ = g²` (`SinglePolymerGaussian`,
via `SumOfSquares.q_mul_self_nonneg`); `freeTotalVariance_eq` is the honest additivity/
factorisation of the finite product over the `b⁴` sites.

---

## 2. The FREE Ursell VANISHING — the adversarial refutation of the dodge

| declaration | content | axioms |
|---|---|---|
| `freeJoint2`, `freeConnected2` | joint 2-point `⟨A_x A_y⟩` (= `⟨A_x⟩⟨A_y⟩` by independence) and connected part | — |
| **`freeConnected2_eq_zero`** | **`⟨A_x A_y⟩ − ⟨A_x⟩⟨A_y⟩ = 0`** for distinct sites (independence factorises the joint moment) | propext |

**Decisive finding (sympy exact).** For the FREE (independent) product measure the connected
two-point between distinct sites is **exactly 0**, so the free product measure has
`z_n(multi-site) = 0` for every `n ≥ 2`: **it carries NO interaction.** Consequently
inhabiting `treeDom` via the free measure is a **free-field DODGE** — it satisfies the letter
of the tree bound (`zAmp ≡ 0 ≤ mu^n·(z_1)^n`) while capturing none of the physical interaction.

`freeKPAmplitude_of_single : SinglePolymerActivity afr → KPAmplitude afr` makes this explicit:
given only the single-site scalar, the free route (`zAmp ≡ 0`) produces a full `KPAmplitude`
with **vacuous** `treeDom`. This is the Rule-9(6) vacuity in slow motion — and precisely why
`treeDom` is not genuine content on its own.

---

## 3. The Mayer/Ursell field structure and the `treeDom` reduction

| declaration | content | axioms |
|---|---|---|
| `singleLine_ursell_discharged` | the Mayer/Ursell tree structure GENUINELY discharged in ONE instance — the PROVED single-line chain `MayerClustering.mayerUrsell_singleLine` (connected correlator ≤ spanning-cluster envelope `C·ρ^n`) | propext, Quot.sound |
| `FieldMeasureSubstrate` (structure) | bundles the GENUINE finite-block content (`siteScale`, `siteVariance_nonneg`, `single : SinglePolymerActivity`) with the OPEN `wickTreeDom` | — |
| **`treeDom_of_substrate`** | **the reduction**: a `FieldMeasureSubstrate` produces the full `KPAmplitude` (whose `amplitude_le`/`clusterSum_le` are PROVED); `treeDom` is REDUCED to `wickTreeDom`. CONDITIONAL producer | propext, Quot.sound |

`FieldMeasureSubstrate.wickTreeDom : ∀ k n, zAmp k n ≤ mu^n·(z1 k)^n` is the **named
residual**: that the INTERACTING (physical, generally NONZERO) connected n-cluster amplitude
is tree-dominated. This is the config-space Gaussian-integral **Wick content** (Wick/Isserlis
for the interacting weight `e^{−S_int}` against the finite Gaussian reference) — the object
the free product measure cannot supply (its `z_n≥2` vanish) and the character-basis library
lacks. `mayerUrsell_singleLine` shows the tree-dominated Ursell structure exists in ONE real
instance (the 1D chain); the 4D field-measure generalisation is the residual.

---

## 4. Numeric validation (`fieldmeasure_verify.py`, mpmath dps 50, sympy exact)

1. **Single-mode `z₁`**: `z₁(w) = 1 − e^{−g²/4}(1 − g²/2) ≤ g²` for all `w∈(0,1)`, worst
   ratio → `3/4` (`max(z₁ − g²) = −2.5e−5 < 0`). Confirms the single-site scalar.
2. **The `{+s,−s}` surrogate law (sympy exact)**: `⟨A⟩=0`, `⟨A²⟩=s²` (variance matched),
   but `⟨A⁴⟩ = s⁴ ≠ 3s⁴` (true-Gaussian 4th moment). **HONEST**: the minimal law is a
   *variance-matched surrogate*, not the true Gaussian — it carries the 2nd moment (`z₁`),
   not the higher Wick structure (`z_{n≥2}`).
3. **Finite product**: total variance `Σ_{x<m} s² = m·s²`; `Ξ_free = Z1^m`; `log` additive.
4. **Free connected 2-point** `⟨A_x A_y⟩ − ⟨A_x⟩⟨A_y⟩ = 0` — the free-field dodge exposed.
5. **KP tree bound** `|z_n| ≤ (μg²)^n`, `μ=6`: converges `⟺ w > 5/6` (deep-UV / continuum).
6. **`b⁴` sites**: `b=2⟹16`, `b=3⟹81`, `b=4⟹256` — finite ⟹ constructible.
7. **`g²` bracket** `(1−w) ≤ −log w ≤ (1−w)/w` holds on the grid.

---

## 5. Cascade / STOP status (mandatory task condition ii)

**No STOP condition tripped. No guarded bundle inhabited.**

- `treeDom` is **NOT** genuinely built (only the free-field dodge + the reduction to the named
  `wickTreeDom` residual). `FieldMeasureSubstrate` is **UNINHABITED**.
- `treeDom_of_substrate` and `freeKPAmplitude_of_single` are **CONDITIONAL producers** (open
  binders on `FieldMeasureSubstrate` / `SinglePolymerActivity`) — they inhabit `KPAmplitude`
  (a non-guarded node) only relative to an open input; they do **NOT** unconditionally inhabit
  `FieldClusterConvergence`, and do NOT cascade to `SingleCouplingFormPreservation → continuum
  floor → FrontierDAG.trueMargin`.
- Full build: `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`
  (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) —
  UNCHANGED. Nothing inhabited or weakened.

---

## 6. HONEST FOUNDATIONAL ASSESSMENT (adversarial)

**Can the Lean-core constructive library carry the finite-lattice field measure + the
Mayer-Ursell structure?**

- **YES for the FINITE, FREE single-block measure.** The finite-lattice PRODUCT of the proved
  single-mode Gaussians is genuinely constructible (`freeTotalVariance_eq`: `Σ_{x<m} s² ≃
  m·s²`), and its partition function factorises (`freePartition`). Built here, axiom-clean.

- **NO for the genuine `treeDom`.** The free product measure's Ursell expansion is **trivial**
  — every multi-site connected amplitude vanishes (`freeConnected2_eq_zero`) — so inhabiting
  `treeDom` via the free measure is a **free-field dodge** (`freeKPAmplitude_of_single`,
  `zAmp ≡ 0`), NOT the real Ursell structure. Two independent reasons the free route is
  inadequate: (i) independence kills `z_{n≥2}`; (ii) even the single-mode law is only
  variance-matched (`⟨A⁴⟩ = s⁴ ≠ 3s⁴`), so it lacks the Gaussian Wick moments the interacting
  `z_n` are built from.

- **The genuine residual (named, not faked): `FieldMeasureSubstrate.wickTreeDom`** — the
  config-space Gaussian-integral Wick tree domination of the INTERACTING connected amplitudes
  `|z_n| ≤ μ^n·(z_1)^n`. Deriving it needs the config-space measure with its interaction
  weight `e^{−S_int}` and Wick's/Isserlis' theorem for the Gaussian integral — **the actual
  4D-YM measure construction, a NEW SUBSTRATE the character-basis library lacks.**

- **The FURTHER residual: the continuum / infinite-volume measure.** The FINITE single-block
  measure is finite/constructible (built here). The full field integral over the infinite
  lattice and the `a → 0` scaling limit are a **separate, further** residual on top of
  `wickTreeDom`.

**Verdict.** `treeDom` is **REDUCED, not BUILT**: the finite-block FREE field measure is
constructed genuinely (finite product of proved single-mode Gaussians), the free-field dodge
is formally exposed and refuted (`freeConnected2_eq_zero`), and the genuine content is
precisely named as `wickTreeDom` (the config-space Gaussian Wick expansion of the interacting
`z_n`), with the continuum/infinite-volume measure as the further residual. No guarded frontier
bundle is inhabited; nothing is faked; **the 4D Yang–Mills mass gap remains OPEN.**

---

## 7. Build / guard / axioms (honesty gate)

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (701 jobs).
```

`#print axioms` for all 10 load-bearing declarations: `[propext]`, `[propext, Quot.sound]`, or
**empty** (`blockSites_two`, `freePartition_succ`). NO `Classical.*`, no `sorryAx`, no
`native_decide`, no `sorry`/`admit` (banned tokens appear only inside the axiom-gate docstring
prose). All witnesses `Type`-level.
