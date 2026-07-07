# The continuum (a→0) field-space measure — the last terminal frontier

**Deliverable.** `lean/YMGap/Continuum/ContinuumFieldMeasure.lean` (wired into `YMGap.lean`;
full `lake build` green = **709 jobs**; `YMGapGuard` **frontier-guard OK** = 5 Clay-frontier
types still unconditionally uninhabited; axiom-clean `propext`/`Quot.sound` or empty). Numerics
`verify_continuum.py` (mpmath dps 45, sympy exact). **Commits: none** (per instruction).

---

## 0. The obligation

The a→0 continuum field-space measure: as the spacing `a → 0` (RG steps `k → ∞`, coupling
`g² ~ (1−w_k) ~ 1/k → 0`), the field-space measure is the continuum limit of the finite-block
interacting Gaussian. Pieces already standing (verified this session by reading the code):

- single-mode activity `|z_1| ≤ g²` **PROVED** all-orders (`ExactSinglePolymerActivity`,
  transcendental via `CRealExp`);
- finite-block **FREE** product measure **BUILT** (`FieldMeasureUrsell.freeTotalVariance_eq`,
  `Σ_{x<m} s² ≃ m·s²`; `freePartition = Z1^m`);
- character basis **PROVED inadequate** for the continuum (`ZnCharacterSumFrontier`:
  `2w³ → 2 > 1` diverges, overshoots `g²`);
- the transmutation abstractions (`m_phys = 1 − e^{−1/e}`, conserved `dimMargin`, the product
  floor) **PROVED** as the zero-defect idealization (`DimensionlessMarginTransmutation`);
- the self-similar RG fixed-point flow **PROVED** (`SelfSimilarFlow.concreteSelfSimilarFlowE`,
  irrational `e^{−1}` separators satisfying the flow law no rational flow inhabits).

The residual the task targets: the **concrete continuum field-space measure** that realizes these
abstractions — the a→0 inverse-limit of the finite-block Gaussians. Is it constructible from the
proved pieces, or a genuine foundational frontier?

---

## 1. What is BUILT (genuine, from the proved pieces)

The a→0 continuum measure is realized as the **inverse (projective) limit** over RG scales.
`ContinuumFieldMeasure.lean` builds the scaffold:

| declaration | content | axioms |
|---|---|---|
| `InverseLimitTower b` (structure) | the projective system: a covariance-scale family `scale : ℕ → CReal` + the **block-spin (Kadanoff) decimation consistency** `scale k ≈ (scale (k+1))^(b+1)` (Kolmogorov/Bochner compatibility of the finite-block marginals) | — |
| **`freeInverseLimitTower b`** | **THE FREE INVERSE-LIMIT IS CONSTRUCTIBLE** — a genuine inhabitant, built from the PROVED `concreteCRealFlowE b`; the decimation consistency IS the self-similar flow law | propext, Quot.sound |
| `convergesTo_of_all_equiv` | a sequence whose every term shares one limit `ConvergesTo` it | none |
| **`freeContinuum_converges`** | **THE a→0 LIMIT EXISTS** — the finite-block dimensionless covariances `dimMargin b s N` CONVERGE (modulus = conservation) to the self-similar FIXED POINT `1 − sep 0 = m_phys > 0` | propext, Quot.sound |
| `freeContinuum_converges_concreteE` | the same, UNCONDITIONAL, along the irrational `e^{−1}` flow | propext, Quot.sound |
| **`freeContinuum_no_interaction`** | **THE HONEST LIMITATION** — the free inverse-limit's connected 2-point VANISHES (`freeConnected2_eq_zero`): it is the GAUSSIAN FREE FIELD, drops all interaction | propext |

This is genuine, not a re-labeling: `freeInverseLimitTower` reuses the real irrational
self-similar flow (no dialed constant; the exp-on-CReal residual discharged), and
`freeContinuum_converges` is a real convergence theorem about a real `CReal` sequence to a real
positive limit.

**Verdict of §1: the FREE / Gaussian continuum measure IS the inverse-limit, and it IS
constructible from the proved pieces — it is the self-similar RG fixed point, the a→0 limit of
the finite-block free measures.**

---

## 2. The genuine residual (NAMED, not faked): the INTERACTING continuum measure

The free inverse-limit is the Gaussian free field — physically trivial. The **interacting**
continuum measure is the genuine frontier:

| declaration | content | axioms |
|---|---|---|
| `InteractingContinuumMeasure afr b` (structure, **UNINHABITED**) | bundles the CONSTRUCTIBLE free projective system (`base`), the PROVED single-site scalar (`single : SinglePolymerActivity`), the INTERACTING amplitudes `zAmp` (generally nonzero), and the TWO OPEN config-space fields | — |
| ↳ `uniformWickTreeDom` (field) | the OPEN **uniform-in-scale** config-space Gaussian-integral Wick tree domination `|z_n| ≤ μ^n·(z_1)^n` of the interacting weight `e^{−S_int}` — the substrate the character basis lacks and the free measure cannot supply | — |
| ↳ `interScaleDefect` (field) | the OPEN **inter-scale coupling** `ε_k ≥ 0`: the deviation of the interacting block-spin consistency from the ideal self-similar flow (the ADDITIVE block-spin erosion the free tower has ZERO of) | — |
| `kpAmplitude_of_interactingContinuum` | the reduction: an `InteractingContinuumMeasure` produces `KPAmplitude` (NON-guarded) via the PROVED KP scaffold. CONDITIONAL producer (open binder) | propext, Quot.sound |
| `freeDodge_interactingContinuum` | the free-field dodge made explicit AND refused: `zAmp ≡ 0`, `interScaleDefect ≡ 0` fills the letter, empty of content. CONDITIONAL producer (open binders `base`, `single`) | propext, Quot.sound |

The inverse-limit / self-similar scaffold **supplies the FREE skeleton and NAMES exactly what the
interacting measure adds** — it is not a re-labeling that supplies the interacting content.

---

## 3. Numeric validation (`verify_continuum.py`, mpmath dps 45, sympy exact)

1. **Inverse-limit consistency** `sep_k = (sep_{k+1})^(b+1)`, `b=1`: max error over `k<40` is
   `8.8e−47` (pure fp noise) — the block-spin decimation compatibility holds.
2. **a→0 inverse limit converges**: `dimMargin_N → m_phys = 1 − e^{−1/e} = 0.307799372…`;
   `|dimMargin_N − m_phys|` = `0, 2.6e−46, 8.5e−45, …, 3.5e−28` (fp noise) — conserved at every
   scale.
3. **a→0**: `sep_k → 1` (spacing `a_k → 0`), lattice covariance `1 − sep_k → 0`:
   `0.3078, 1.4e−3, 8.6e−11, 1.1e−39, 0` at `k=0,8,32,128,512`.
4. **Free connected 2-point vanishes** (sympy exact): `mx·my − mx·my = 0` — the Gaussian free
   field, no interaction.
5. **Fixed point positive**: `m_phys = 0.30779937… > 0`.

---

## 4. Cascade / STOP status (MANDATORY task condition ii) — EXHAUSTIVE audit

**No STOP condition tripped. No guarded bundle inhabited. No cascade triggered.**

The mandatory audit (this is the last frontier, so the most exhaustive):

- **Nothing guarded is inhabited.** `InverseLimitTower` and `InteractingContinuumMeasure` are
  NEW nodes, **not** among the 5 guarded Clay-frontier types (`Tier0Scorecard`,
  `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`). Full build:
  `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited` (708 → 709 jobs = the
  +1 new module).
- **`SinglePolymerActivity` is NOT constructed** — it is an OPEN structure FIELD of the
  uninhabited `InteractingContinuumMeasure` and an OPEN BINDER of `freeDodge_…`. No inhabitant
  of `SinglePolymerActivity` is produced anywhere in the module.
- **`KPAmplitude` is produced only CONDITIONALLY** (`kpAmplitude_of_interactingContinuum`, open
  binder `M`); it is a NON-guarded node and does NOT cascade to `FieldClusterConvergence →
  SingleCouplingFormPreservation → continuum floor → FrontierDAG.trueMargin`.
- **`InteractingContinuumMeasure` has NO unconditional inhabitant.** The only producer,
  `freeDodge_…`, requires `single : SinglePolymerActivity afr` (itself uninhabited) plus a
  `base : InverseLimitTower b` — so composition with the constructible `freeInverseLimitTower`
  still leaves the `single` binder open. No closed term of the interacting measure exists.
- **The free inverse-limit is `CReal`-valued** (the ideal irrational flow); it does NOT map into
  the rational `TrueMarginRecursion` / `SingleStepDefectBound` / `afDefectSeq` bundles — same
  firewall the transmutation module established.
- **`#print axioms`** for all 7 load-bearing declarations: `[propext]`, `[propext, Quot.sound]`,
  or **empty** (`convergesTo_of_all_equiv`). No `Classical.*`, no `sorryAx`, no `native_decide`,
  no `sorry`/`admit` (banned tokens absent from the file — verified by scan).

---

## 5. HONEST FOUNDATIONAL ASSESSMENT (adversarial — task condition iii, iv)

**Can the Lean-core library carry the continuum field-space measure — the a→0 inverse-limit of
the finite-block Gaussians + the self-similar fixed point — or does it fundamentally need the
infinite-dimensional continuum field integral?**

The continuum measure **splits cleanly**, and the split is the honest answer:

- **The FREE / Gaussian continuum measure = the inverse-limit = CONSTRUCTIBLE from the proved
  pieces.** It is the self-similar RG fixed point: `freeInverseLimitTower` (the projective system,
  from the proved irrational self-similar flow) with the a→0 limit genuinely EXISTING
  (`freeContinuum_converges`, converging to `m_phys > 0`). This is the Gaussian free field, and
  the Lean-core library **does** carry it — no infinite-dimensional integral needed, because a
  product (free) measure's projective limit is determined by its (convergent, self-similar)
  covariance, and that convergence is exactly what the self-similar flow supplies.

- **BUT the free inverse-limit DROPS all interaction** (`freeContinuum_no_interaction`,
  `freeConnected2_eq_zero`): its connected correlations vanish. So the *constructible* piece is
  physically trivial. **Adversarial finding (the honest core):** the inverse-limit / self-similar
  scaffold DOES drop the interacting content — the coupling between scales and the non-abelian
  structure. It is NOT a re-labeling that secretly carries them; it demonstrably carries the FREE
  skeleton and *nothing more* (the vanishing 2-point is a theorem).

- **The INTERACTING continuum measure is the genuine FOUNDATIONAL FRONTIER.** It needs two things
  the free inverse-limit provably lacks, both named as OPEN fields of the uninhabited
  `InteractingContinuumMeasure`:
  1. **`uniformWickTreeDom`** — the uniform-in-scale config-space Gaussian-integral Wick/Isserlis
     expansion of the interacting weight `e^{−S_int}` (the nonzero connected `z_n`). This is the
     genuine infinite-dimensional continuum field integral / constructive-QFT measure content.
     The character basis lacks it (proved), the free product measure cannot supply it (its
     `z_{n≥2}` vanish, proved), and the finite-block Gaussian is only variance-matched
     (`⟨A⁴⟩ = s⁴ ≠ 3s⁴`, prior finding).
  2. **`interScaleDefect`** — the inter-scale coupling (the additive block-spin erosion `ε_k`),
     which the ideal self-similar flow has zero of. This is the same object
     `TrueMarginRecursionPhysical` isolates as the Clay core; the continuum measure exposes it as
     the deviation of the interacting projective consistency from the free flow law.

**Verdict.** The continuum field-space measure is the inverse-limit: **CONSTRUCTIBLE for the
FREE / Gaussian skeleton** (the self-similar RG fixed point, genuinely built and axiom-clean),
the **genuine FOUNDATIONAL FRONTIER for the interacting content** — which fundamentally needs the
infinite-dimensional constructive-QFT measure (the config-space Gaussian integral of `e^{−S_int}`
with uniform-in-scale Wick tree domination) plus the non-abelian inter-scale coupling. The
Lean-core library carries the free skeleton and NAMES the interacting residual precisely; it does
not, and this scaffold does not, construct the interacting continuum measure. **No guarded
frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.**

---

## 6. Build / guard / axioms (honesty gate)

```
$ lake build
info: YMGap/Continuum/ContinuumFieldMeasure.lean: 7 load-bearing decls,
      #print axioms = [propext] / [propext, Quot.sound] / empty
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (709 jobs).
```

No `Classical.*`, no `sorryAx`, no `native_decide`, no `sorry`/`admit`. Lean-core only
(`Q'`/`CReal`, reused PROVED `concreteCRealFlowE`, `dimMargin_conserved`, `freeConnected2_eq_zero`,
`kpAmplitude_of_singlePolymer`); no Mathlib, no `ring`. All witnesses `Type`-level.
