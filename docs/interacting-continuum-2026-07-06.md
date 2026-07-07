# The two open fields of `InteractingContinuumMeasure` — connected, reduced, and the decisive non-closure audit

**Deliverable.** `lean/YMGap/Continuum/InteractingMeasureReduction.lean` (wired into
`YMGap.lean`; full `lake build` green = **710 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited; every load-bearing decl axiom-clean
`[propext, Quot.sound]`, no `sorry`/`sorryAx`/`native_decide`/`Classical.*`). Numerics
`verify_imr.py` (mpmath dps 50, sympy exact). **Commits: none** (per instruction).

---

## 0. The obligation

`ContinuumFieldMeasure.InteractingContinuumMeasure afr b` (`Type`, UNINHABITED = the a→0
interacting config-space measure) bundles the CONSTRUCTIBLE free projective skeleton
(`base : InverseLimitTower b`) and the single-site scalar (`single : SinglePolymerActivity afr`)
with the amplitudes `zAmp` and **two OPEN config-space fields**:

- `uniformWickTreeDom : ∀ k n, zAmp k n ≤ mu^n·(single.z1 k)^n` — the uniform-in-scale Wick
  domination of the interacting connected amplitudes;
- `interScaleDefect : Nat → Q'` (nonneg) — the additive block-spin erosion `ε_k`.

The task: connect each to the proved pieces; decide whether they REDUCE (⟹ the measure closes,
cascade to the mass gap) or expose the genuine free-interacting-integral frontier — with maximal
scrutiny and an exhaustive audit if anything closes.

---

## 1. Reduction 1 — `uniformWickTreeDom` ⟵ per-scale Penrose/SOS chain + `pertRep`

`uniformWickTreeDom` has **exactly the shape** of `FieldMeasureUrsell.FieldMeasureSubstrate.
wickTreeDom` (`∀ k n, zAmp k n ≤ mu^n·(z_1)^n`). The already-PROVED chain, all steps `∀ k n`:

```
pertRep        |z_n| ≤ |C(G)|·prop^n        (IsserlisPenroseData — Feynman / signed-Ursell rep)
  → isserlisBound  |z_n| ≤ count(n)·prop^n     via PROVED penroseIneq : |C(G)| ≤ τ(G)
  → wickTreeDom    |z_n| ≤ mu^n·(z_1)^n        via SOS wickEdgeBound (prop ≤ z_1) + count ≤ μ^n
```

Every step is **`k`-independent** (the SOS edge bound is per-`k`, the Penrose signed cancellation
per-`n`, the animal count uniform), so the chain is **automatically uniform in the RG scale `k`**.

`interactingMeasure_of_penrose` (new, PROVED axiom-clean) makes this machine-checked: from an
`IsserlisPenroseData afr` — whose SOLE open field is `pertRep` — plus a `base` and an erosion
sequence, it BUILDS an `InteractingContinuumMeasure afr b` whose `uniformWickTreeDom` **is** the
PROVED `fieldMeasureSubstrate_of_penrose D |>.wickTreeDom`. So **`uniformWickTreeDom` reduces to
`pertRep`** (the perturbative representation of `z_n`), the SOS off-diagonal edge bound + Penrose
cancellation + count all discharged.

**Where the field-space convergence enters (and where it does NOT).** `g² = 1 − w_k → 0` (proved,
`FieldSpaceCluster`) is what makes the KP cluster **SUM** finite: `μg² < 1` ⟹ `Σ|z_n| ≤ 1/(1−μg²)`
(`clusterSum_le`), and `interacting_amplitude_le` re-exposes `|z_n| ≤ (μg²)^n` for the measure's
amplitudes. **But convergence is NOT needed for the per-term tree-domination bound** — that is the
per-scale Penrose/SOS chain above. So `uniformWickTreeDom` = per-scale Penrose/SOS (PROVED) +
`pertRep` (open); the shrinking activity `g² → 0` is a separate, orthogonal, proved input.

Numeric (dps 50): `g² = −log w`, `μ = 6`: `μg² = 0.632, 0.060, 0.0060` at `w = 0.9, 0.99, 0.999`
(all `< 1`, KP converges); Penrose `|C(K_n)| = (n−1)! = 1,2,6,24,120,720 ≤ τ(K_n) = n^{n−2} =
1,3,16,125,1296,16807` (n = 2..7) — the signed cancellation is real.

---

## 2. Reduction 2 — `interScaleDefect` ⟵ the telescoping eigenvalue-shift budget

`AnchorDominance` PROVED (axiom-clean): the multiplicity-blind eigenvalue shift
`ε_k = w_{k+1}³ − w_k³` **telescopes** — `∑_{j<K} ε_j ≃ w_K³ − w_0³ ≤ 1 − w_0³` — so the ENTIRE
accumulated additive erosion is the single **closed** value `1 − w_0³`.

`interScaleDefect_tailSum_le` / `interScaleDefect_floor` (new, PROVED axiom-clean) transport this
to the structure's field: for an `InteractingContinuumMeasure M` with
`M.interScaleDefect = eigShiftSeq w` (the AF flow),

- `∑_{j<K} M.interScaleDefect j ≤ 1 − w_0³` for every window `K` (via `eigShift_tailSum_le`);
- with the additive step `margin(k+1) ≥ margin k − M.interScaleDefect k` and anchor-dominance
  `1 − w_0³ < margin 0`, the PROVED `anchorDominance_floor` yields the uniform strictly-positive
  continuum floor `margin 0 − (1 − w_0³) > 0` (∀ k).

Numeric (exact + dps 50): at the deep-UV anchor `w_0 = 11/12`, `1 − w_0³ = 397/1728 = 0.229745…`
`< 3/10 ≤ m_phys = 1 − e^{−1/e} = 0.307799…`, slack `0.078054…`; telescope verified EXACT to
`K = 1000` on a concrete AF flow.

So **`interScaleDefect` reduces to the eigenvalue-shift telescoping**: the *summability* and
*anchor-dominance* — carried by CAPSTONE §5 as an independent open inequality — are **PROVED**.
Two real-flow inputs stay OPEN: (i) the **identification** `interScaleDefect = eigShiftSeq w` for
the REAL 4D block-spin flow (Route I's UNINHABITED `EigenvalueShiftDefect`); (ii) the
**transmutation anchor** `margin 0 ≥ m_phys` for the real flow. Note also that in the structure
`interScaleDefect` is a free nonneg sequence *not referenced by any other field's type* — it is
decorative until identified with `eigShiftSeq w`, so the reduction is exactly "the proved budget
holds *once you supply the (open) identification*."

---

## 3. THE DECISIVE CHECK — does `InteractingContinuumMeasure` close?  **NO. z_n is a FREE field.**

Both reductions are genuine progress, but they sit on top of **two irreducible free inputs**, each
requiring the actual interacting configuration-space Gaussian integral:

**(A) `pertRep : |z_n| ≤ |C(G)|·prop^n` — the CONSTRUCTION of `z_n`.** This is the assertion that
the interacting connected amplitude `z_n` equals the signed-Ursell / Feynman-diagram sum from
expanding `e^{−S_int}` against the Gaussian reference — i.e. `z_n = ∫ e^{−S_int}·(cluster) / Z`.
In the structure, `zAmp` (`= z_n`) is a **FREE field**: `uniformWickTreeDom` only bounds it from
ABOVE. Machine-checked in the new file:

- `interacting_zAmp_free_dodge` : `(freeDodge_interactingContinuum base single).zAmp = fun _ _ => 0`
  — the free-field dodge inhabits the WHOLE structure with `zAmp ≡ 0` (every connected amplitude
  vanishes, `freeConnected2_eq_zero`: NO interaction);
- `interacting_zAmp_of_penrose` : `(interactingMeasure_of_penrose D …).zAmp = D.zAmp` — an
  arbitrary `pertRep`-supplied `zAmp`.

The constructor accepts BOTH ⟹ **`z_n` is underdetermined by the structure**. The measure DEFINES
`z_n`; it does not construct it. This is the circularity the task warns about: the KP/Wick/Penrose
machinery **bounds** `z_n` *given it exists*; it does not produce `z_n = ∫e^{−S_int}χ/Z`.

**(B) the real-flow transmutation identification** `interScaleDefect = eigShiftSeq w` + the anchor
`margin 0 ≥ m_phys` — Route I's UNINHABITED `EigenvalueShiftDefect` and the real-flow dimensional
transmutation.

Additionally the single-site scalar `single : SinglePolymerActivity afr` is itself a free/open
input (`z1` free, bounded by `g²`; `ExactSinglePolymerActivity` proves `z_1 ≤ g²` only for the
single-mode Gaussian MODEL, as a `CReal.leRat`, not as an inhabitant tied to the interacting
measure). So the interacting measure has **three** unconstructed measure quantities (`z_1`, `z_n`,
the real erosion), all bounded by proved inequalities but none constructed.

**Verdict: `InteractingContinuumMeasure` does NOT close.** Any closed inhabitant is the free-field
dodge (Gaussian free field, `freeConnected2_eq_zero`), which is **REFUSED** (Rule 9). `z_n` remains
the genuine **free interacting-integral frontier**.

---

## 4. MANDATORY cascade / STOP audit (exhaustive — this is the mass gap)

**No STOP condition tripped. No guarded bundle inhabited. No cascade triggered.**

- **Nothing guarded is inhabited.** `interactingMeasure_of_penrose` is a CONDITIONAL producer with
  OPEN binders (`D` — carrying the open `pertRep`, `hDC`, `single` — plus `base`, `isd`). It does
  NOT unconditionally inhabit `InteractingContinuumMeasure`, and that type is a NEW node, not one of
  the 5 guarded Clay-frontier types (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`,
  `ClayTargetPinned`, `FrontierDAG`). Full build: `frontier-guard OK: 5 … unconditionally
  uninhabited`, 710 jobs (709 → 710 = the +1 new module).
- **`interacting_amplitude_le` is CONDITIONAL** (open binder `M : InteractingContinuumMeasure`): it
  produces the KP bound `|z_n| ≤ (μg²)^n` only RELATIVE to the open interacting measure, and does
  NOT cascade to `FieldClusterConvergence → SingleCouplingFormPreservation → continuum floor →
  FrontierDAG.trueMargin`.
- **`interScaleDefect_floor` is CONDITIONAL** (open binders on `w`, `margin`, the identification
  `hid`, the step law, and anchor-dominance): it does NOT construct `TrueMarginRecursionPhysical`,
  `UniformSpacingFloor`, or `FrontierDAG` — the same firewall `anchorDominance_floor` already has.
- **`#print axioms`** for all 6 load-bearing decls: `[propext, Quot.sound]`. No `Classical.*`, no
  `sorryAx`, no `native_decide`, no `sorry`/`admit` (banned tokens absent from code; one appears in
  docstring prose only).

**Genuinely PROVED vs still FREE (the honest ledger):**

| piece | status |
|---|---|
| free/Gaussian inverse-limit continuum measure (`freeInverseLimitTower`, converges to `m_phys>0`) | **PROVED** |
| KP combinatorial scaffold (Penrose `|C(G)|≤τ(G)`, Cayley, Euler, geometric convergence) | **PROVED** |
| SOS off-diagonal edge bound `⟨A_xA_y⟩ ≤ z_1` (no propagator decay needed) | **PROVED** |
| single-mode Gaussian activity `z_1 ≤ g²` all orders (transcendental `CRealExp`) | **PROVED** (model) |
| field-space convergence `g² = 1−w_k → 0` (activity shrinks in continuum) | **PROVED** |
| eigenvalue-shift telescoping + anchor-dominance `1−w_0³ < m_phys` | **PROVED** |
| **`pertRep`: `z_n` = the interacting integral `∫e^{−S_int}χ/Z`** | **FREE** (open) |
| **`single`: the interacting single-plaquette `z_1`** | **FREE** (open) |
| **real-flow identification `interScaleDefect = eigShiftSeq w` + anchor `margin 0 ≥ m_phys`** | **FREE** (open) |

---

## 5. HONEST VERDICT

The two open fields of `InteractingContinuumMeasure` both **reduce to strictly-smaller named
inputs**, machine-checked and axiom-clean:

- `uniformWickTreeDom` ⟶ **`pertRep`** (the Feynman/signed-Ursell representation of `z_n`), with
  the per-scale SOS edge bound + Penrose cancellation + animal count all PROVED and automatically
  uniform in `k`;
- `interScaleDefect` ⟶ the **telescoping eigenvalue-shift budget** `1 − w_0³ < m_phys` (PROVED),
  leaving the real-flow identification + transmutation anchor.

But **`InteractingContinuumMeasure` does NOT close**, and the reason is exactly the circularity the
task isolates: the measure **DEFINES** `z_n` (a free field bounded above by `uniformWickTreeDom`;
inhabited with `zAmp ≡ 0` by the free-field dodge), it does not **CONSTRUCT** it. The KP/Wick/Penrose/
telescoping machinery is a tower of *conditional bounds on free data*. Constructing `z_n =
∫e^{−S_int}χ/Z` (`pertRep`) and the interacting `z_1` (`single`), and identifying the real
inter-scale erosion — the actual infinite-dimensional interacting configuration-space Gaussian
integral — is the genuine 4D-YM foundational frontier, which the character-basis library lacks.

**No guarded frontier bundle is inhabited; the free-field dodge is refused; nothing is faked; the
4D Yang–Mills mass gap remains OPEN.** `z_n` is the free interacting-integral frontier — located
exactly, not closed.

---

## 6. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (710 jobs).
```

`InteractingMeasureReduction.lean`, 6 load-bearing decls, all `#print axioms = [propext,
Quot.sound]`. Lean-core only (`Q'`/`CReal`, reused PROVED `fieldMeasureSubstrate_of_penrose`,
`eigShift_tailSum_le`, `anchorDominance_floor`, `kpAmplitude_of_interactingContinuum`,
`freeDodge_interactingContinuum`); no Mathlib, no `ring`, no `native_decide`. All witnesses
`Type`-level.
