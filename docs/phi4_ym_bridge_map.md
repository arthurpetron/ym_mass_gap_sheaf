# φ⁴ → YM bridge map: mapping, adversarial audit, and the single-obligation bridge design

**Task:** DEEPEN the φ⁴→YM bridge. φ⁴ validated the spacing-uniform continuum *plumbing*
(`Phi4ScalingBand : RegScalingBand`) with a **dialed-in** `physGapMin = 1`. YM's difficulty is
**dimensional transmutation**: `latMargin j = m_lat(a_j) → 0`, yet `physGap j = m_lat(a_j)/a_j`
must stay `≥ Δ > 0` via AF running. This document (1) maps the exact Lean apparatus, (2) gives a
per-piece satisfiable/defective verdict with evidence, (3) designs the YM-shaped `RegScalingBand`
whose floor is generated (not dialed) and reduces to a SINGLE open obligation, and (4) gives a
phased Lean-core build plan.

All file paths are absolute-relative to
`/Users/darthur/Dore Dropbox/Arthur Petron/claude_folders/ym_mass_gap_sheaf/lean/`.

---

## 0. HEADLINE FINDINGS (read first)

1. **The task's premise is slightly mislabeled — and the correction matters.** There is **no**
   `RegularContinuumPipeline.RegScalingBand.ofDimensionalTransmutation` constructor. `RegScalingBand`
   has exactly **two** real inhabitation routes: raw field-assembly (what `phi4ScalingBand` used) and
   `RGGapPersistence.toScalingBand` (the YM route). The `ofDimensionalTransmutation` symbol lives on the
   **`UniformSpacingFloor`** unifier (`UnifiedContinuumFloor.lean:155`), and it is only a *repackaging*
   of `CodynamicHierarchical.DimensionalTransmutation.rate_matched` into a units-rescaled floor — it is
   **not** a band constructor. **Consequence:** φ⁴ and YM inhabit `RegScalingBand` through the *same*
   assembly; the ONLY difference is how the field `physGapMin_pos` / `physGap_ge` gets discharged.
   The whole "bridge" is therefore about that one discharge, not about a different constructor.

2. **The AF apparatus IS satisfiable but inhabits a SURROGATE, not the physics.**
   `UniformCouplingFromAF.afDefectGapRecursion` / `DominantModeRecursion` genuinely inhabit
   `DefectGapRecursion` / `RubricUniformInCoupling`, but with `physGap k = ∏_{i<k}(1 − δ_ren)` — the
   **survival product**, whose `recursion` field holds **by definitional equality**
   (`physGap (k+1) = physGap k · (1 − δ_k)`). This is *not* the true dimensionless margin
   `Δ_k = m_lat(a_k)/a_k`. The code says so verbatim (`UniformCouplingFromAF.lean:36-41, 275-287`).
   So the AF machinery produces *a positive number*, not *the physical band floor*. Not defective —
   but its satisfiability is "cheap" and does not touch transmutation.

3. **The genuine YM bridge object already exists structurally: `RGGapPersistence`.** Its `atSpacing j`
   carries the fixed-spacing cluster bound at `a_j` with `floorRate = m_lat(a_j)` (the TRUE lattice
   gap, not a surrogate), its physical gap is `divPos(m_lat(a_j))(a_j) = m_lat(a_j)/a_j` (the TRUE
   ratio), `toScalingBand` assembles the `RegScalingBand`, and the `j=0` anchor rung is PROVED
   (`anchor_physGap_pos`, `mFiducial = 999/1000`). Its SOLE open field is
   `physFloor : ∀ j, c ≤ m_lat(a_j)/a_j`.

4. **The single irreducible obligation, sharpest form: `TrueMarginRecursionPhysical`.** The true
   margin obeys an **ADDITIVE-erosion** step `margin(k+1) ≥ (1−δ_k)·margin_k − ε_k`, for which
   summability of `∑(δ+ε)` does **not** force a positive limit — you need the *anchor-dominates-budget*
   condition carried as data. **Every** inhabited surrogate in the codebase is purely multiplicative
   (no `ε`), so it structurally evades exactly the hard part. This is the honest YM delta.

5. **No glue lemma yet connects `TrueMarginRecursionPhysical` to `RGGapPersistence`/`RegScalingBand`.**
   (Verified by grep — empty.) That glue (margin = `m_lat/a`, feeding `physFloor`) is the one genuinely
   *new, Lean-core-buildable* reduction the bridge needs; the obligation it consumes is the Clay core.

---

## 1. THE APPARATUS MAP (exact Lean + what each requires)

### 1.1 The transmutation constructor (the "form φ⁴ did NOT use")

**`UniformSpacingFloor.ofDimensionalTransmutation`** — `UnifiedContinuumFloor.lean:155-163`:

```lean
def ofDimensionalTransmutation
    (D : CodynamicHierarchical.DimensionalTransmutation) :
    UniformSpacingFloor (fun (q : Q') (p : Q' × Q') => q * p.1 ≤ p.2)
      (fun N : Nat => (D.aScaling N,
        ((1 : Q') - D.sep N)
          * CodynamicHierarchical.physMultiplierProduct D.bb D.sep N)) where
  floor := D.physFloor
  floor_pos := D.physFloor_pos
  bound := D.rate_matched
```

It requires a `DimensionalTransmutation` (`CodynamicHierarchical.lean:275-314`), whose open field is:

```lean
  rate_matched : ∀ N : Nat,
    physFloor * aScaling N ≤ ((1 : Q') - sep N) * physMultiplierProduct bb sep N
```

with hardening fields `aScaling_step` (`aScaling(k+1)·(bb k+1) = aScaling k`, ties spacing to block
factors), `sep_mono`, and `sep_to_one` (`∀ε>0, eventually 1 − sep k ≤ ε` — forces genuine continuum
approach; a constant `sep` is *excluded*, `constSep_violates_sep_to_one`). `physMultiplierProduct` is
`∏_{k<N} rhoDecimate(bb k, sep k)`, the exact heat-kernel decimation product. This is a *different,
units-rescaled* packaging of the same open floor: `physFloor·a ≤ (1−sep)·∏ρ_dec`.

**What it requires vs. `RGGapPersistence`:** both encode "positive floor below a per-scale physical
gap." `DimensionalTransmutation` rescales by the decimation product `∏ρ_dec` and the spacing; it is
strictly *more elaborate* (and more constrained) than the plain `RGGapPersistence.physFloor`
`c ≤ m_lat(a_j)/a_j`. φ⁴ used neither — it assembled `RegScalingBand` raw (`Phi4ScalingBand.lean:223`).

### 1.2 The RG-flow defect product floor — `DefectGapRecursion`

`ContinuumClosureProgram.lean:136-162`. The `recursion` field (the ledger's "unproved for 4D"):

```lean
  recursion : ∀ k : Nat, (1 - defect k) * physGap k ≤ physGap (k + 1)
```

plus `physGap0_pos`, `defect_nonneg/le_one`, `prodFloor_pos`, and
`prodFloor_le : ∀ k, prodFloor ≤ prodPrefix (fun i => 1 − defect i) k · physGap 0`.
`DefectGapRecursion.uniform_floor` (PROVED, `:219`) distills these to `prodFloor ≤ physGap k` by a
product induction — the genuine reduction content. `continuum_floor_of_defectRecursion`
(`ContinuumClosureProgram.lean:302`) turns it into the positive continuum floor.

### 1.3 The dimensionless scale normalization — `RGLandingInput` / `RGLandingCertificate`

`RGLandingCertificate.lean:98-139`. `RGLandingCertificate` asserts a positive rational `q` with the
division-free `ofQ' q · Λ_YM ≤ m` (i.e. `q ≤ m/Λ_YM`). The **open** input is `RGLandingInput D`
(`:98`): supplies `massScale = m`, `lambdaYM = Λ_YM > 0`, and

```lean
  ratio_bound : CReal.mul (CReal.ofQ' D.prodFloor) lambdaYM ≤ massScale
```

The only constructor `rgLanding_of_input` (`:159`) is CONDITIONAL — it takes `RGLandingInput` and sets
`q := D.prodFloor` (positivity from `D.prodFloor_pos`). No unconditional inhabitant of `RGLandingInput`.

### 1.4 The AF running

**`FourDExistence.lean`** (finite, PROVED):
- `betaZero c2adj := (11/3)·c2adj` (`:145`); `betaZero_pos` (`:283`): `hveeFloor ≤ c2adj ⇒ 0 < β₀`
  (dual-Coxeter floor `hveeFloor = 2`, attained at SU(2)).
- `invRunningCoupling u0 c2adj k := u0 + β₀·k` (`:149`); `invRunningCoupling_strictMono` (`:305`):
  `u(k) < u(k+1)` — `g²` decays logarithmically toward the UV with the correct one-loop sign.

**`AFRateModulus`** (`AFRateCalibration.lean:767-789`): the two-loop rate as a NAMED interface —
`rate_upper: 1 − w_k ≤ A/(k+B)` and `rate_lower: A'/(k+B) ≤ 1 − w_k` (i.e. `1 − w_k ≍ g_k² ≍ 1/k`).
Concrete inhabitant `afRateModulus_canonical` (`:796`, `w_k = 1 − 1/(k+1)`). **NOT derived** — AF physics input.

**`AFRateCalibration` proves a NEGATIVE diagnostic** (`:641 harmonic_diverges`, `:1015
linear_bound_not_summable`): the LINEAR bond-moving budget `∑ 6p·(1−w_k)` is bounded below by a
divergent harmonic series, so the linear crack **cannot** be summable. The renormalized **quadratic**
defect `δ_ren ≤ C·(1−w)²` (`∑1/k² < ∞`) is what is required.

**`SummabilityCapstone`** supplies that quadratic defect and its product floor:
`renDefect afr p k := bondMovingDeltaRen 1 p (afr.w k)` (`:190`, dominant `s=1`, fusion degree `N=1`),
`renDefect_le_half` (`:410`, tail `k ≥ defectCutoff`), and
`renormalized_gap_of_AFRate afr p` (`:526`): PROVED positive product floor `ε > 0` on the tail rate
`ρ_j = 1 − δ_ren(w_{k₀+j})`. **SCOPE flagged in code:** dominant `s=1` mode, `N=1`, renormalized
(marginal flow absorbed), tail `k≥k₀` — full-mode/genuine-trajectory is open.

**`UniformCouplingFromAF`** wires AF → recursion:
- `afDefectGapRecursion afr : DefectGapRecursion` (`:175`) — `physGap := ∏(1−δ_ren)` (survival product);
  `recursion` holds by `Q'.mul_comm` (definitional). `prodFloor := afFloorEps afr` from the capstone.
- `dominantModeRecursion_of_AFCertificate C` (`:212`) — same, at `afRateModulus_of_AFCertificate C`.
- `rubricUniformInCoupling_certified` (`:226`) — unconditional on the decidable `O4Model`.

**`AFTrajectoryCertificate`** (`:137`) + `AFCertificateModel.O4Model` (`:275`, `τ_k = 1/(k+2)`, `β=1`,
`E=1`): a genuine two-loop recurrence-with-cubic-remainder (`recurrence`, `drop_core`) yielding an
`AFRateModulus` via `afRateModulus_of_AFCertificate` (`:380`). Honest, decidable, non-defective.

### 1.5 The fixed-spacing gap that feeds `latMargin`

`RealCorrMass.lean`: `realLocated Λ := reconTransfer_located_gap Λ` (`:112`), separator
`sep = rho gw = 2·(1/6)³ = 1/108`, **margin `1 − rho = 107/108`** (`realCorr_margin`, `:227`),
derived from the REAL `wilsonG` connected-correlator decay. Volume-independent (same at every `Λ`),
floor `1/2 ≤ 107/108` (`decide`). This is the numerator `m_lat` at **fixed strong coupling**. The
`RGGapPersistence` anchor uses `NonSaturatedFloor.mFiducial = 999/1000` at `a_0 = 1`
(`RGGapPersistence.lean:324-357`).

### 1.6 The YM-side band bridge that already exists

`RGGapPersistence` (`RGGapPersistence.lean:107-127`): `atSpacing j` = fixed-spacing cluster bound at
`a_j`, `floorRate = m_lat(a_j)`; open field
`physFloor : ∀ j, floorConst ≤ Q'.divPos ((atSpacing j).floorRate) (spacing j) _` (i.e.
`c ≤ m_lat(a_j)/a_j`); `toScalingBand` (`:143`) assembles the `RegScalingBand`
(`physGapMin := floorConst`, `physGap_ge := physFloor`). Per-block form `RGBlockPersistence` (`:199`)
packages the open content as `rho_k · (m_lat(a_k)/a_k) ≤ m_lat(a_{k+1})/a_{k+1}` (`recursion`, `:223`)
+ product floor — a `DefectGapRecursion` whose `physGap` **is** the true band quotient. Anchor rung PROVED.

---

## 2. PER-PIECE VERDICT (satisfiable vs. defective) — adversarial

| Apparatus piece | Lean | Verdict | Evidence |
|---|---|---|---|
| `UniformSpacingFloor.ofDimensionalTransmutation` | `UnifiedContinuumFloor.lean:155` | **SATISFIABLE (trivial repackaging)** | Total `def`, axiom-gated. Just projects `DimensionalTransmutation` fields into the unifier. Not load-bearing itself. **Mislabel flag:** it is NOT a `RegScalingBand` constructor. |
| `DimensionalTransmutation` (the underlying open struct) | `CodynamicHierarchical.lean:275` | **SATISFIABLE, non-vacuous, correctly NAMED-OPEN** (not defective) | Hardened against the constant-`sep` gaming exploit: `sep_to_one` + `constSep_violates_sep_to_one`; `marginProduct_pos` (`:321`) forces `0 < (1−sep_N)·∏ρ_dec` at every `N`, so degenerate `sep=1` collapse excluded. No YM inhabitant. **Adversarial note:** it is *more constrained* than `RGGapPersistence` (extra `∏ρ_dec`/`aScaling_step` coupling) — a heavier obligation than needed. Prefer `RGGapPersistence`. |
| `DefectGapRecursion.recursion` | `ContinuumClosureProgram.lean:151` | **SATISFIABLE by surrogate; genuine-margin form OPEN** | `trivialDefectGapRecursion` (δ=0) non-vacuity witness (`:253`); genuine inhabitant `afDefectGapRecursion` uses **survival-product surrogate**, recursion by definitional equality. Not defective, but does NOT carry the true margin. |
| `RGLandingInput` | `RGLandingCertificate.lean:98` | **UNINHABITED by design (the wall) — honest** | No unconditional constructor; `q = D.prodFloor` tied to real machinery (`rgLandingCertificate_q_eq_prodFloor`). Correctly named-open. |
| `RGLandingCertificate` | `RGLandingCertificate.lean:125` | **SATISFIABLE only via the conditional reduction** | `rgLanding_of_input` CONSUMES `RGLandingInput`. Honest. |
| `FourDExistence.betaZero_pos` | `:283` | **PROVED (unconditional, finite)** | `β₀ = 11/3·c2adj > 0` for `c2adj ≥ 2`. Correct one-loop AF sign. Axiom-gated. |
| `FourDExistence.invRunningCoupling_strictMono` | `:305` | **PROVED (unconditional, finite)** | `u(k) = u0 + β₀·k` strictly increasing. Correct AF running. |
| `AFRateModulus` | `AFRateCalibration.lean:767` | **SATISFIABLE (named interface)** — NOT derived | `afRateModulus_canonical` concrete; 1/k two-loop rate is honest AF *input*, explicitly not proved. |
| `AFRateCalibration.linear_bound_not_summable` | `:1015` | **PROVED (real negative diagnostic)** | Harmonic divergence via doubling blocks; rules out the linear crack. This is a genuine sharpening, not a stub. |
| `SummabilityCapstone.renormalized_gap_of_AFRate` | `:526` | **PROVED, but SCOPE-LIMITED (dominant s=1, N=1, renormalized, tail)** | Real inverse-square summability ⇒ `e^{−2R}` product floor. Full-mode content OPEN (flagged in code). Not defective; not sufficient. |
| `UniformCouplingFromAF.afDefectGapRecursion` / `dominantModeRecursion_of_AFCertificate` | `:175 / :212` | **SATISFIABLE (surrogate) — grounds a positive number, not the physics** | `physGap = survival product`; `recursion` definitional. The genuine content pinned in `TrueMarginRecursion` is left UNINHABITED (`:245`). |
| `AFCertificateModel.O4Model` | `:275` | **HONEST decidable inhabitant (not defective)** | `τ_k=1/(k+2)`, genuine two-loop `recurrence` via `recurrence_bound`/`drop_core`, `τ_lower` with `B=4`. |
| `reconTransfer_located_gap` / `realCorr` (fixed-spacing) | `RealCorrMass.lean:112, 227` | **PROVED (genuine Wilson-correlator gap)** | margin `107/108` from real `wilsonG` decay; volume-independent. This is the honest `m_lat` at fixed coupling. |
| `RGGapPersistence.physFloor` + `toScalingBand` | `RGGapPersistence.lean:123, 143` | **OPEN field (the Clay core); reduction PROVED; anchor rung PROVED** | `toScalingBand` pure assembly; `anchor_physGap_pos` unconditional; `physFloor` uninhabited for `j→∞`. |
| `TrueMarginRecursionPhysical` | `TrueMarginRecursionPhysical.lean:102` | **UNINHABITED (the sharpest honest residual)** | Additive-erosion `step` + anchor-dominates-budget carried as data; `uniformSpacingFloor_of_trueMarginPhysical` (adequacy) PROVED. |

**No defective (provably-false / vacuous / over-general) atom found in the transmutation apparatus.**
Unlike the finite Tier-0 atoms (SixJPentagon false, A2 vacuous, DCHyp over-general), the AF/transmutation
pieces are honestly named-open or genuinely proved. The **only** integrity issue is the *labeling*
subtlety of finding #1 and the *surrogate-vs-true-margin* gap of findings #2/#4 — which are honestly
disclosed in the code's own docstrings, not hidden defects. The heaviest-obligation piece
(`DimensionalTransmutation`, with its `∏ρ_dec`/`aScaling_step` coupling) is *over-specified* relative to
the minimal `RGGapPersistence.physFloor`; the bridge should route through the latter.

---

## 3. THE BRIDGE DESIGN — YM-shaped `RegScalingBand` with a GENERATED floor

### 3.1 The target band

Define the YM band as `toScalingBand P` for a YM `P : RGGapPersistence` (NOT raw φ⁴ assembly):

- `spacing j := a_j` (e.g. `2^{-j}`, or a bare-coupling-driven schedule `a(g_j)` with `g_j = g(a_j)`
  the AF-running coupling; `spacing_pos` trivial).
- `atSpacing j :=` the fixed-spacing infinite-volume cluster bound at coupling `g(a_j)`, whose
  `floorRate = m_lat(a_j)` is the **genuine** strong-coupling spectral gap (anchor `j=0` uses the
  PROVED `reconTransfer_located_gap`/`mFiducial`; general `j` requires the fixed-spacing bound to hold
  along the AF window — the SZZ/Bałaban content).
- `physGap j := Q'.divPos (m_lat(a_j)) (a_j) = m_lat(a_j)/a_j` — **derived** (theorem
  `physGap_spacing`), never dialed.
- `physGapMin := floorConst = c`, `physGapMax := ceilConst = C`.
- `physGap_ge := physFloor`, `physGap_le := physCeil`.

Then `band_physGapMin_pos` and `band_gap_survives` fire exactly as on φ⁴ — the plumbing is identical.
The floor `c` is now *generated* (`= D.prodFloor` from an AF `DefectGapRecursion`, or the
`floorWitness` of a `TrueMarginRecursionPhysical`), not `= 1` by `decide`.

### 3.2 The single reduced obligation (stated EXACTLY)

The band `physGapMin > 0` reduces — with all φ⁴-validated mechanics reused — to inhabiting **one**
structure. Sharpest honest form (`TrueMarginRecursionPhysical.lean:102`), specialized to YM:

> **YM TRANSMUTATION OBLIGATION.** There exist a lattice-mass family `m_lat : ℕ → Q'`, an AF spacing
> schedule `a : ℕ → Q'` (`a_k > 0`, `a_k → 0` as `g(a_k) → 0`), per-step defect `δ_k ≥ 0` (the
> non-abelian multi-link block-spin bond-moving defect) and additive erosion `ε_k ≥ 0`, such that the
> **true dimensionless margin** `margin k := m_lat(a_k)/a_k` satisfies
>
> - **`step`** (additive-erosion block-spin law): `∀k, (1 − δ_k)·margin_k − ε_k ≤ margin_{k+1}`;
> - **`budget_modulus`** (explicit tail rate, not bare `Summable`):
>   `∀ N M, tailSum (δ+ε) N M ≤ budgetTailConst · pot 2 N`;
> - **anchor-dominates-budget** (carried as DATA): a rational `floorWitness > 0` and a `CReal Δ` with
>   `ofQ' floorWitness ≤ Δ` and `∀k, leEv Δ (ofQ' (margin k))`.

Equivalently, discharging the `physFloor` field of the YM `RGGapPersistence`:
`∃ c > 0, ∀ j, c ≤ m_lat(a_j)/a_j`, with `m_lat(a_j) = (atSpacing j).floorRate` the PROVED
fixed-spacing gap and `a_j → 0` along asymptotic freedom. `uniformSpacingFloor_of_trueMarginPhysical`
(`:164`, PROVED) already turns the sharp form into the `QFloor`/`UniformSpacingFloor` `c`, and
`toScalingBand` turns that into the band — so once the obligation is inhabited, `physGapMin > 0` is a
theorem.

**Why this is genuinely single and irreducible.** The multiplicative surrogate (`afDefectGapRecursion`)
already inhabits the *product-recursion* form for free (definitional). The obligation that resists is
the **`step` with the additive `−ε_k`** term plus the **anchor-dominates-budget** positivity — because
for an additive recursion, `∑(δ+ε) < ∞` alone does **not** imply a positive limit
(`TrueMarginRecursionPhysical.lean:22-28`, verbatim). The `ε_k` is the vacuum-shift / multi-link
non-abelian composition defect that no character-diagonal or perturbative estimate can supply
(`character_window_excludes_weak` caps at `w = 2^{−1/3}`). This is the Bałaban/Shen–Zhu–Zhu class object.

### 3.3 φ⁴ TRANSFERS vs. YM DELTA

**Transfers (validated plumbing, reused verbatim):**
- `SpectralModel → LocatedSpectralGap → RegUniformClusterBound → completeLimit → positive RegularCReal`
  on non-degenerate Cauchy data.
- The `divPos` derivation `physGap j = latMargin j / a_j` with `physGap_spacing` a THEOREM; the
  two-sided `physGap_ge`/`physGap_le`; `band_gap_survives`, `band_physGapMin_pos`.
- `RegScalingLimitModulus` (`RegularContinuumPipeline.lean:611`) convergence (`physMod`, `physBound`),
  `bareCoupling : ℕ → Q'` as data, and `band_collapse_of_modulus` RG-invariance.
- `RGGapPersistence.toScalingBand`, `RGBlockPersistence.toUniform`,
  `uniformSpacingFloor_of_trueMarginPhysical` — the assembly is spacing-agnostic and fires identically.

**YM delta (does NOT transfer — the irreducible core):**
- The discharge of `physGapMin_pos`/`physFloor`. φ⁴ set `physGapMin = 1` by `decide` (a bare-mass
  rational fact). YM must generate `c > 0` from {AF-running `δ_k`, summable via `renDefect`/`AFRateModulus`}
  × {fixed-spacing `m_lat`} — which reduces to the **additive-erosion `step` + anchor-dominates-budget**
  of §3.2. φ⁴ has no `ε_k` (super-renormalizable, mass-tuned), so it exercises none of this.
- The persistence of the fixed-spacing gap `m_lat(a_j)` along the AF window for `j ≥ 1` (only `j=0`
  proved). This is coupled to the same obligation.

---

## 4. LEAN-CORE FEASIBILITY — phased build plan

**Buildable NOW (structural reduction wiring; no new substrate primitives):**

- **P1 — `YMScalingBand.lean` skeleton.** A YM `RGGapPersistence` with `spacing j := aSeq j`
  (`2^{-j}`), `atSpacing j :=` a coupling-scheduled cluster-bound family whose `floorRate` reuses the
  PROVED `reconTransfer_located_gap`/`concreteClusterBound` at the anchor and a NAMED family elsewhere,
  and `physFloor`/`physCeil` as the two **named-open** fields. Emit `toScalingBand` → `RegScalingBand`,
  fire `band_gap_survives`. The `j=0` rung is unconditional (`anchor_physGap_pos`). *Mirrors
  `phi4ScalingBand` but leaves `physFloor` open instead of `decide`.* Compiles, axiom-clean.

- **P2 — the new glue lemma `regScalingBand_of_trueMarginPhysical`.** Take a
  `TrueMarginRecursionPhysical T` whose `margin k = m_lat(a_k)/a_k` matches an `RGGapPersistence`'s
  `atSpacing`/`spacing` (via `margin_def` + `latMargin_eq`), and produce the `physFloor` field
  (`floorConst := T.floorWitness`) through `uniformSpacingFloor_of_trueMarginPhysical` +
  `le_of_leEv_ofQ'`. **This is the missing reduction** (grep-confirmed absent) and is pure `Q'`/`CReal`
  wiring — the single highest-value buildable deliverable. Yields `physGapMin > 0 ⇐ TrueMarginRecursionPhysical`.

- **P3 — AF-provenance wiring.** Show the surrogate `afDefectGapRecursion afr`
  (`δ_k = renDefect`, `prodFloor = afFloorEps`) supplies the *multiplicative* half and the summable
  `budget_modulus` shape (via `renormalized_gap_of_AFRate` + `AFRateModulus`), and connect
  `betaZero_pos`/`invRunningCoupling_strictMono`/`O4Model` as the AF-running provenance for `δ_k`.
  Emit a lemma that a YM `TrueMarginRecursionPhysical` **with `ε ≡ 0`** collapses to the proved
  surrogate — making explicit that the ONLY residual field is the additive `ε_k` + anchor-dominates-budget.

- **P4 — dimensionless normalization.** Wire `RGLandingCertificate.rgLanding_of_input` so the generated
  `c = floorConst` is presented as the dimensionless `c ≤ m/Λ_YM` (RG-invariant), reusing the proved
  reduction. Compiles conditionally on `RGLandingInput` (uninhabited).

**NAMED-OPEN (NOT buildable — the Clay core, do not fake):**

- **The inhabitant of `TrueMarginRecursionPhysical` for YM** — specifically its `step` (the additive
  non-abelian multi-link 4D block-spin margin law) and `floorWitness`/`lowerBound`
  (anchor-dominates-budget). Equivalently the `RGGapPersistence.physFloor` for general `j`. This is the
  spacing-uniform gap persistence of Bałaban / Shen–Zhu–Zhu; it is `character_window_excludes_weak`-hard
  and cannot be discharged in Lean-core (nor anywhere, yet).

**Honest scope statement for the build:** P1–P4 ISOLATE the minimal open input inside a compiling,
axiom-clean reduction — they carry the whole weight onto one named `Type`, exactly as
`uniformSpacingFloor_of_trueMarginPhysical` intends. They do **not** close transmutation. The deliverable
is the reduction chain `YM RegScalingBand.physGapMin > 0 ⇐ RGGapPersistence.physFloor ⇐
TrueMarginRecursionPhysical (additive step + anchor-dominates-budget)`, with the AF running supplying
everything *except* the additive erosion term — that term is the Clay core.

---

## 5. One-paragraph summary

The YM transmutation apparatus is honest and (mostly) satisfiable, with **no defective atom** of the
SixJPentagon kind — but two integrity subtleties dominate. (1) There is no `RegScalingBand`
transmutation constructor; φ⁴ and YM share the same `toScalingBand`/raw assembly, so the entire bridge is
the discharge of one field, `physFloor : ∀j, c ≤ m_lat(a_j)/a_j`. (2) The AF machinery
(`afDefectGapRecursion`, `renormalized_gap_of_AFRate`, `O4Model`) genuinely inhabits the *multiplicative
survival-product surrogate* but not the *true physical margin*; the difference is precisely the
**additive-erosion term `ε_k`** in `TrueMarginRecursionPhysical.step`, for which summability does not
imply positivity — so the single irreducible obligation is that additive block-spin law plus an
anchor-dominates-budget witness carried as data. The bridge is buildable up to and including a new glue
lemma `RegScalingBand.physGapMin > 0 ⇐ TrueMarginRecursionPhysical` (P2, currently absent), with the AF
running supplying every input except `ε_k`; that `ε_k` is the Clay core and stays uninhabited.
