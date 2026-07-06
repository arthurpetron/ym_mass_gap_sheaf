# φ⁴ (d = 2,3) validation of the spacing-uniform continuum pipeline — scoping doc

**Track B1, WORK-PLAN-2026-07-05.** Model-problem-first: demonstrate that the project's
single binding continuum object (`UniformSpacingFloor` / `ContinuumGapPersistence` /
`RegScalingBand`) is *usable end-to-end* on a theory that is actually provable, before the
YM-specific attack. φ⁴₂,₃ is the right model because its gap comes from a **tunable bare
mass** (put in by hand), so it exercises the pipeline's convergence/tightness plumbing
**without** needing non-perturbative gap generation.

**One-line thesis.** φ⁴ can inhabit *every* structural field of the continuum interface —
including `physGapMin_pos`, the field that is open for YM — but it inhabits that field for a
*different reason* (a dialed-in bare mass, a rational fact) than YM needs (dimensional
transmutation, `exp(−1/g²)`, an open non-perturbative fact). φ⁴ validates the plumbing; it
does not, and cannot, validate the YM physics.

---

## 1. The EXACT interface a φ⁴ inhabitant must supply

All quotes are the live field shapes. Substrate = custom constructive Lean (`Q'` rationals,
`CReal`/`RegularCReal` reals, no Mathlib). Two limits are kept rigorously separate: **Λ→∞
at fixed spacing** (proved, unconditional) and **a→0 scaling** (the open frontier).

### 1a. Finite-volume spectral datum — `SpectralGap.SpectralModel` + `LocatedSpectralGap`

`lean/YMGap/Continuum/SpectralGap.lean:102` and `LocatedSpectralGap.lean:128`:

```lean
structure SpectralModel where
  k : Nat                          -- number of spectral modes (finite at fixed volume)
  w : QSeq                         -- spectral weights w_i = |⟨Ω, A i⟩|² ≥ 0
  lam : QSeq                       -- transfer eigenvalues λ_i = e^{-E_i} ≥ 0
  w_nonneg   : ∀ i, (0:Q') ≤ w i
  lam_nonneg : ∀ i, (0:Q') ≤ lam i
-- corr S n = Σ_{i<k} w_i · λ_i^n   (connected two-point fn at separation n)

structure LocatedSpectralGap (S : SpectralModel) : Type where
  sep : Q'                         -- located separator (upper bound on excited spectrum)
  sep_lt_one : sep < (1:Q')        -- THE gap
  bound : SpectralGapBound S sep   -- ∀ i, S.lam i ≤ sep
-- .gapMargin = 1 − sep ;  .decay : corr S n ≤ corr S 0 · sep^n
```

### 1b. Infinite-volume (Λ→∞), fixed spacing — the UNCONDITIONAL cluster bound

`RegularContinuumPipeline.lean:114` (`RegUniformClusterBound`) and its equivalent
`ContinuumGapLimit.lean:79` (`ContinuumGapPersistence`). The two carry the same shape; the
pipeline one packages the modulus as `ModCauchy`-level `Q'` data:

```lean
structure RegUniformClusterBound : Type where
  gaps       : Nat → SpectralModel                       -- finite-volume model at each Λ
  located    : (Λ:Nat) → LocatedSpectralGap (gaps Λ)     -- PROVED located gap at each Λ
  floorRate  : Q'                                        -- uniform positive floor δ
  floorRate_pos : (0:Q') < floorRate
  uniform_floor : ∀ Λ, floorRate ≤ (located Λ).gapMargin -- NO-COLLAPSE as volume grows
  M          : Q' → Nat                                  -- outer Cauchy modulus (Type data)
  Mmono      : ∀ ε δ, 0 < δ → δ ≤ ε → M ε ≤ M δ
  bound      : ∀ ε, 0 < ε → ∀ i j, M ε ≤ i → M ε ≤ j →   -- geometric cluster tail as modulus
      (located i).gapMargin ≤ (located j).gapMargin + ε ∧
      (located j).gapMargin ≤ (located i).gapMargin + ε
```

`ContinuumGapPersistence` (`ContinuumGapLimit.lean:79`) is the `CReal` twin: same
`gaps/located/floorRate/floorRate_pos/uniform_floor`, plus a `continuumRate : CReal`, a
`converges : ConvergesTo (fun Λ => ofQ' (located Λ).gapMargin) continuumRate`, and
`floor_persists : ofQ' floorRate ≤ continuumRate`. From either, positivity of the continuum
rate is a **theorem** (`continuum_mass_isPositive`, `regClusterBound_isPositive_gap`) —
`⟨floorRate, floorRate_pos, floor_persists⟩` is literally an `IsPositive` certificate.

### 1c. The a→0 scaling interface — `RegScalingBand` (PRIMARY) and `RegScalingLimitModulus`

`RegularContinuumPipeline.lean:446` — the modulus-free, Clay-relevant obligation:

```lean
structure RegScalingBand where
  spacing     : Nat → Q'                                 -- lattice spacings a_j → 0
  spacing_pos : ∀ j, (0:Q') < spacing j
  atSpacing   : Nat → RegUniformClusterBound             -- fixed-spacing bound at each a_j
  physGapMin  : Q'                                       -- uniform PHYSICAL lower bound
  physGapMax  : Q'                                       -- uniform PHYSICAL upper bound
  physGapMin_pos : (0:Q') < physGapMin                   -- ← THE OPEN CONTENT (for YM)
  physGap_ge : ∀ j, physGapMin ≤ divPos (atSpacing j).floorRate (spacing j) _
  physGap_le : ∀ j, divPos (atSpacing j).floorRate (spacing j) _ ≤ physGapMax
-- physGap j := divPos (latMargin j) (a_j) ;  latMargin j := (atSpacing j).floorRate  (→0 like a_j)
-- physGap_spacing (THEOREM): physGap j · a_j ≃ latMargin j
```

The physical gap `Δ(a_j) = latMargin j / a_j` is a **derived rational quotient**
(`divPos`), so its defining relation is a theorem, not assumed. Headlines
`band_physGapMin_pos` and `band_gap_survives` (`ofQ' physGapMin ≤ ofQ' (physGap j)`, uniform
in `j`) say *liminf physGap ≥ physGapMin > 0* — "the gap survives a→0" — without asserting a
limit exists.

The stronger refinement `RegScalingLimitModulus` (`:611`) `extends RegScalingBand` with
`spacingMod`/`spacing_to_zero` (a_j→0), `bareCoupling : Nat → Q'` (the RG bare coupling as
data), and a spacing-uniform two-sided convergence modulus `physMod/physMod_mono/physBound`
on `j ↦ physGap j`. From it, `scaling_continuum_physGap` (a `completeLimit`) and its
positivity `scaling_continuum_physGap_isPositive` build the continuum physical gap as a
positive `RegularCReal`; `band_collapse_of_modulus` makes it a unique RG-invariant.

### 1d. The unifier — `UniformSpacingFloor` and its five constructors

`UnifiedContinuumFloor.lean:93`:

```lean
structure UniformSpacingFloor {ι α} (le : Q' → α → Prop) (g : ι → α) : Type where
  floor     : Q'
  floor_pos : (0:Q') < floor
  bound     : ∀ i, le floor (g i)
```

Constructors that extract each wall into this one shape (`:120–164`):
`ofUniformPhysGapFloor` (codynamic CReal gap), `ofModeEnergyFloor` (curvature `Q'`
energies), **`ofContinuumGapPersistence`** (`QFloor (fun Λ => (P.located Λ).gapMargin)`,
floor `= P.floorRate`), `ofUniformRatioVariation` (the `Δ/√σ̂` ratio), and
**`ofDimensionalTransmutation`** (the spacing-matched product
`q·aScaling ≤ (1−sep)·∏ρ_dec`, floor `= physFloor`). The capstone `unified_continuum_gap`
(`:250`) drives BOTH the codynamic and curvature routes from one shared `floor`.

**File header, verbatim honesty (`:46`):** "`UniformSpacingFloor` is itself UNINHABITED for
the genuine continuum (a→0): it IS the open dimensional-transmutation / spacing-uniform
spectral-gap physics (Bałaban / Shen–Zhu–Zhu class). Nothing here inhabits it for 4D
Yang–Mills."

---

## 2. The φ⁴-inhabitable vs NOT-inhabitable field map

The pivotal physics distinction. YM's gap is **dimensional transmutation**: a classically
scale-invariant action generates a physical scale `Λ_YM = a⁻¹exp(−1/(2β₀g²))`
non-perturbatively; the lattice gap `m_lat(a)→0` like `a`, and `physGapMin > 0` is *forced
by the theory's own dynamics with no mass parameter to dial*. φ⁴₂,₃ is **super-renormalizable
with a relevant bare mass `m₀²`**: you tune `m₀²(a)` directly to hold the physical
correlation length `ξ = 1/m_phys` fixed as `a→0`. So for φ⁴ the positivity `physGapMin > 0`
is a *dialed-in rational fact*, not a non-perturbative miracle.

| Interface field | φ⁴ status | why |
|---|---|---|
| `SpectralModel` (`k,w,lam,…`) | **INHABITABLE** | φ⁴ transfer matrix is positive, reflection-positive; finite volume ⇒ finite/compact spectrum. Rational envelope from the cluster expansion. |
| `LocatedSpectralGap.{sep,sep_lt_one,bound}` | **INHABITABLE** | high-T / weakly-coupled φ⁴ has a located gap `sep = e^{−m·a} < 1`. |
| `floorRate`, `floorRate_pos`, `uniform_floor` (volume-uniform floor) | **INHABITABLE** | φ⁴ in the high-T phase has *volume-uniform* exponential clustering (Glimm–Jaffe–Spencer; Bauerschmidt–Dagallier). This is real content, not fiducial. |
| `M`, `Mmono`, `bound` / `converges` (convergence modulus) | **INHABITABLE — the key plumbing being validated** | the φ⁴ cluster/RG expansion gives an *explicit convergence rate* ⇒ an explicit `ModCauchy` modulus on the margin sequence. |
| `floor_persists` (floor survives Λ→∞) | **INHABITABLE** | uniform clustering ⇒ the floor passes to the limit. |
| `continuumRate`, `continuum_mass_isPositive` | **INHABITABLE (derived)** | positivity is a *theorem* from the two above. |
| `spacing`, `spacing_pos`, `atSpacing` (a→0 sequence of bounds) | **INHABITABLE** | pick `a_j = 2⁻ʲ`; supply a φ⁴ cluster bound at each `a_j` with the bare mass tuned to hold `m_phys` fixed. |
| **`physGapMin_pos`, `physGap_ge`, `physGap_le`** (the two-sided PHYSICAL band) | **INHABITABLE for φ⁴ — for a DIFFERENT reason than YM** | tune `m₀²(a_j)` so `latMargin j ≈ m_phys·a_j` ⇒ `physGap j = latMargin/a_j ≈ m_phys ∈ [m_phys/2, 2m_phys]`. Positive because the bare mass was dialed in. **This is the whole point: φ⁴ CAN inhabit the field that is OPEN for YM.** |
| `RegScalingLimitModulus.{physMod,physBound}` (a→0 convergence) | **INHABITABLE (sharpest)** | the φ⁴ continuum limit *exists* (Glimm–Jaffe φ⁴₃; Feldman–Osterwalder), so `physGap j → m_phys` with an explicit rate ⇒ an explicit `physMod`. |
| `bareCoupling : Nat → Q'` (AF running) | **INHABITABLE as data, but TRIVIAL content** | φ⁴₂,₃ has no asymptotic freedom; `bareCoupling` is a directly-tuned relevant parameter, not a logarithmically-running `g₀(a)→0`. |
| **`ofDimensionalTransmutation`** route: `physFloor·aScaling ≤ (1−sep)·∏ρ_dec` | **NOT the φ⁴ route** | the RHS is generated by the AF RG flow with `∏ρ_dec` decimation factors; φ⁴ has no such transmutation product. φ⁴ inhabits `UniformSpacingFloor` via the **plain-floor** `ofContinuumGapPersistence` / `RegScalingBand` route, not the spacing-matched transmutation route. |
| The *mechanism* behind `physGapMin_pos` (non-perturbative scale generation) | **NOT INHABITABLE / NOT VALIDATED by φ⁴** | φ⁴ gets the floor from a bare mass; YM must get it from `DefectGapRecursion.recursion` (Bałaban-class RG). This is the open YM core and φ⁴ says nothing about it. |

**Crisp summary.** φ⁴ inhabits *every structural field* of
`RegUniformClusterBound` / `ContinuumGapPersistence` / `RegScalingBand` /
`RegScalingLimitModulus`, and inhabits the open field `physGapMin_pos` too — but by a
**rational, tuned-bare-mass** argument, discharging it through the `ofContinuumGapPersistence`
plain-floor constructor, **not** through `ofDimensionalTransmutation`. The
convergence/tightness *machinery* is validated; the non-perturbative *gap-generation
mechanism* is neither exercised nor validated.

---

## 3. Literature — the sharpest spacing-uniform φ⁴ statement and its constructive content

**Classical constructive φ⁴ with a mass gap, uniform in the cutoff.**
- Glimm, Jaffe, Spencer, *The Wightman axioms and particle structure in the P(φ)₂ model*,
  Ann. Math. **100** (1974) — high-temperature / weak-coupling cluster expansion; mass gap
  and exponential clustering for P(φ)₂, uniform in volume.
- Feldman, Osterwalder, *The Wightman axioms and the mass gap for weakly coupled φ⁴₃*,
  Ann. Phys. **97** (1976) 80–135; Magnen–Sénéor — φ⁴₃ construction with a **positive mass
  gap uniform in the lattice/UV cutoff**; O(4)/Euclidean invariance and exponential
  clustering survive the continuum limit.
- Glimm–Jaffe, *Quantum Physics* (and the tutorial CQFT lectures) — the canonical
  statement: renormalized correlation functions obey bounds **uniform in the lattice spacing
  a**; lattice Schwinger functions converge as tempered distributions with a strictly
  positive, volume-independent spectral gap for the continuum Hamiltonian.

**The sharpest modern spacing-uniform statement (recommended anchor).**
- **Bauerschmidt & Dagallier, *Log-Sobolev inequality for the φ⁴₂ and φ⁴₃ measures*,
  CPAM (2024), arXiv:2202.02295.** Result: the continuum φ⁴₂ and φ⁴₃ measures satisfy a
  log-Sobolev inequality **uniformly in the lattice regularisation**, under the optimal
  assumption of bounded susceptibility — holding for all couplings in finite volume and
  **uniformly in the volume throughout the entire high-temperature phases**. Method: a
  Polchinski (continuous-scale RG) criterion for LSI + a correlation inequality for Ising
  with external fields + Perron–Frobenius + skeleton-inequality susceptibility bounds.
  Companion: *Behavior of the Poincaré constant along the Polchinski flow*
  (arXiv:2208.08186); *Log-Sobolev for near-critical Ising* (arXiv:2202.02301).
  - **Constructive content relevant here.** The uniform LSI/Poincaré constant is exactly a
    *spacing-uniform spectral-gap of the Glauber/Langevin dynamics*, produced by an RG
    (Polchinski) flow with **explicit, spacing-uniform rate estimates** — i.e. precisely a
    concrete `ModCauchy`-type convergence modulus and a uniform floor, the two ingredients
    `RegUniformClusterBound`/`RegScalingLimitModulus` demand. It is the cleanest citable
    source of a *spacing-uniform floor + explicit modulus* for φ⁴.

**Caveat to state honestly in Lean prose.** The Bauerschmidt–Dagallier gap is the *dynamic*
(Dirichlet-form) spectral gap of the sampling process; the *static* mass gap = inverse
correlation length is the Glimm–Jaffe/Feldman–Osterwalder object. In the high-T / weakly-
coupled phase both are positive and spacing-uniform, and both give the rational envelope our
`SpectralModel`/`floorRate` needs. For the φ⁴ *validation* target the relevant import is the
existence of an **explicit spacing-uniform rate**, which both literatures supply.

Related pointer already in project memory: Shen–Zhu–Zhu et al. (rigorous lattice YM,
strong-coupling) is the YM analogue of the *fixed-spacing* content; the φ⁴ literature is what
supplies the *spacing-uniform a→0* content that YM lacks.

---

## 4. The Lean plan — a concrete, minimal φ⁴ `RegScalingBand` inhabitant

**Design principle (matches the project's honesty conventions).** We do **not** build φ⁴ path
integrals. We supply the φ⁴ transfer data as **rational envelopes justified by the cited
spacing-uniform bounds** — exactly as `NonSaturatedFloor` supplies the SU(2) fiducial
`mFiducial = 999/1000` rather than computing SU(2) integrals. The deliverable is: *the a→0
band interface, currently inhabited by NOTHING concrete, admits a non-degenerate concrete
inhabitant whose downstream theorems fire.* That is the validation.

**What is genuinely new vs. what exists.** The current concrete inhabitant
(`concreteContinuumYM`, `concreteClusterBound`) is **constant in volume** (`M ε = 0`) and has
**no scaling/`a→0` structure at all** — it never touches `RegScalingBand`. So *no concrete
object currently exercises*: (i) a non-trivial `ModCauchy` modulus, (ii) the `divPos`
physical-gap derivation across a spacing sequence, (iii) the two-sided `RegScalingBand` band,
(iv) `RegScalingLimitModulus` convergence + `band_collapse_of_modulus`. The φ⁴ target is the
**first concrete inhabitant of the a→0 band**.

**Tractability verdict.** Everything below is **Lean-core tractable**: `Q'` arithmetic,
`divPos` (`RegularCRealArith.lean:105`), `ofQ'`, and the existing `completeLimit`/`ModCauchy`
primitives. **No constructive-integral layer is needed** — precisely because we take the
cluster-expansion output as rational data. (Deriving that data from the φ⁴ action *would*
need the from-scratch integral layer; that is the deliberate boundary of the validation, not
part of the target.)

Phased build (each phase compiles and is axiom-gated `propext`/`Quot.sound`):

- **Phase 1 — `Phi4LatticeData.lean`.** A φ⁴ family parametrised by a physical mass
  `m : Q'` (and a high-T coupling), giving an explicit rational `SpectralModel` per volume
  with `sep` a rational lower model of `e^{−m·a}`, **non-constant in volume** (finite-volume
  correction with an explicit geometric decay). Deliver `phi4ClusterBound m : RegUniformClusterBound`
  with a **non-trivial** modulus `M ε` (real Cauchy data, not `M ε = 0`). *Exercises (i).*
- **Phase 2 — `Phi4Persistence.lean`.** Feed Phase 1 through
  `continuumYM_of_clusterBound` / `ContinuumGapPersistence` to get a φ⁴
  `ConstructiveContinuumYM` and a positive `RegularCReal` continuum gap at fixed spacing —
  now via `completeLimit` on **genuine** Cauchy data. Deliver `phi4_continuum_gap_pos`.
- **Phase 3 — `Phi4ScalingBand.lean` (headline).** Spacings `a_j = 2⁻ʲ`; `atSpacing j =`
  φ⁴ bound with bare mass tuned so `latMargin j ∈ [m/2·a_j, 2m·a_j]`. Then
  `physGap j = divPos (latMargin j) a_j ∈ [m/2, 2m]`, so `physGapMin = m/2`,
  `physGapMax = 2m`, and **`physGapMin_pos` PROVED** by `decide`-level `Q'` arithmetic.
  Deliver `phi4ScalingBand : RegScalingBand` — **the first concrete inhabitant of the a→0
  band that is uninhabited for YM**, plus `band_gap_survives` fired on it. *Exercises (ii),(iii).*
- **Phase 4 — `Phi4ScalingLimit.lean`.** Extend to `RegScalingLimitModulus` with an
  explicit `physMod` (the tuned tolerance gives a geometric convergence rate `physGap j → m`).
  Deliver `scaling_continuum_physGap phi4…` and `…_isPositive` — a genuine (φ⁴, no open
  hypothesis) continuum PHYSICAL mass gap — and `band_collapse_of_modulus` on it.
  *Exercises (iv).*
- **Phase 5 — `Phi4UnifiedFloor.lean`.** Extract the φ⁴ instance as a `UniformSpacingFloor`
  via `ofContinuumGapPersistence` (the plain-floor constructor — **explicitly NOT**
  `ofDimensionalTransmutation`), and show the capstone consumers accept it. Add the honest
  boundary docstring (§5). Deliver the demonstration that the *unifier* is inhabitable by a
  real model.

Estimated effort: Phases 1–3 are the core (finite `Q'`/`divPos`, days-scale); Phase 4 reuses
`completeLimit` wholesale; Phase 5 is wiring. No new substrate primitives required.

---

## 5. HONEST boundary — what φ⁴ success transfers to YM, and what it does NOT

**TRANSFERS (the plumbing).**
- The full data path `SpectralModel → LocatedSpectralGap → RegUniformClusterBound →
  completeLimit → positive RegularCReal`, on **non-degenerate** Cauchy data.
- The `divPos` derivation of the physical gap `Δ(a) = m_lat(a)/a` and the two-sided
  `RegScalingBand` band; the `RegScalingLimitModulus` convergence and the
  `band_collapse_of_modulus` RG-invariance.
- The proof that these interfaces are **correctly shaped and downstream-live**: a real model
  flows through them and the positivity/decay theorems fire. This retires the risk that the
  continuum interface is a formally-stated but unusable stub.
- Confidence that a *spacing-uniform floor + explicit convergence modulus* (the
  Bauerschmidt–Dagallier / Glimm–Jaffe shape) is exactly the right analytic input object.

**DOES NOT TRANSFER (the YM core).**
- **`physGapMin_pos` itself.** φ⁴ discharges it from a **hand-tuned bare mass** — a rational
  fact available because φ⁴ has a relevant mass parameter. YM has **no mass parameter to
  dial**; `physGapMin_pos` must come from **dimensional transmutation** — the non-perturbative
  scale `Λ_YM = a⁻¹exp(−1/(2β₀g²))` generated by the AF RG flow. That is the open field, and
  φ⁴ neither exercises nor informs it.
- **The `ofDimensionalTransmutation` route** (`physFloor·aScaling ≤ (1−sep)·∏ρ_dec`) and its
  AF running `bareCoupling → 0` logarithmically. φ⁴ inhabits the *plain-floor* route only;
  the transmutation product is YM-specific and stays uninhabited.
- **`DefectGapRecursion.recursion` (Bałaban-class 4D RG flow)** — the actual open YM
  analytic input under `RubricUniformInCoupling` and the Tier-0 Stage-2 floor. φ⁴'s
  super-renormalizable, mass-tuned construction does not carry the perturbatively-inaccessible
  content flagged by `character_window_excludes_weak` (`ρ = 2w³ ≥ 1` beyond `w = 2^{−1/3}`).

**One-sentence boundary.** A φ⁴ success proves the continuum *pipeline* is a usable machine
by running a real theory through it end-to-end; it leaves the YM *engine* — non-perturbative
generation of `physGapMin > 0` from a scale-invariant action — exactly as open as before,
because φ⁴ replaces that engine with a bare mass.

---

### Sources
- Bauerschmidt–Dagallier, *Log-Sobolev inequality for the φ⁴₂ and φ⁴₃ measures*, arXiv:2202.02295 (CPAM 2024). https://arxiv.org/abs/2202.02295
- Bauerschmidt–Dagallier, *Behavior of the Poincaré constant along the Polchinski flow*, arXiv:2208.08186. https://arxiv.org/pdf/2208.08186
- Bauerschmidt–Dagallier, *Log-Sobolev inequality for near critical Ising models*, arXiv:2202.02301. https://arxiv.org/abs/2202.02301
- Feldman–Osterwalder, *The Wightman axioms and the mass gap for weakly coupled (Φ⁴)₃*, Ann. Phys. 97 (1976). https://link.springer.com/chapter/10.1007/BFb0013314
- Glimm–Jaffe–Spencer, particle structure / high-temperature expansions, P(φ)₂. https://inspirehep.net/literature/6373
- Jaffe, *Constructive Quantum Field Theory* (tutorial). https://www.arthurjaffe.com/Assets/pdf/CQFT.pdf
