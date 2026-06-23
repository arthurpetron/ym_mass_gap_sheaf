# State of the formalization vs the Clay Yang–Mills requirements (full-tree audit, 2026-06-21)
**STATUS:** Scope/plan dated 2026-06-22; see the canonical ledgers for the outcome (docs/where-the-wall-sits-2026-06-22.md, docs/stage1-completion-ledger-2026-06-22.md, docs/stage2-progress-ledger-2026-06-22.md, docs/continuum-wall-outstanding-2026-06-22.md).

Four independent read-only audits of the entire Lean tree (204 `.lean` files, ~201 imported in
`YMGap.lean`, ~2191 tracked theorems): (A) the mass-gap claim and its dependency closure; (B) the
QFT construction / OS axioms / non-triviality; (C) full-tree soundness & honesty sweep; (D) the
constructive substrate soundness and the critical-path spine. This is the consolidated, honest
accounting. The four agents agree.

## Bottom line

The Clay problem is **OPEN** and this formalization does **not** solve it. What it is: an
**axiom-clean, Mathlib-free, choice-free, `sorry`-free CONDITIONAL factoring** of the Clay distance —
the genuinely-hard content is isolated into explicitly-named, (almost entirely) uninhabited oracle
structures and four `Prop := True` stubs, with a large body of genuinely-proved finite-volume /
fixed-spacing / rational scaffolding underneath. The codebase is, on audit, **as clean and as honest
as it claims** — with a short list of fixable honesty blemishes (below).

## Soundness & hygiene — CONFIRMED (all four agents, mechanically)

- **Zero** genuine `sorry` / `admit` / `sorryAx` / new `axiom` / `native_decide` / `Classical.*` /
  `Choice` / `by_contra` in code (every grep hit is comment prose). **Zero** `import Mathlib`; **zero**
  Lean-core `Real`. The project rolls its own `Q'` *specifically* because Lean's `Rat.decEq` would drag
  `Classical.choice` — principled, not incidental.
- **Axiom-clean**: every tracked theorem reduces to `propext` (often `+ Quot.sound`) only. (Breakdown:
  empty 327, propext 754, propext+Quot.sound 1105, Quot.sound 5 = 2191.)
- **Substrate is SOUND** (agent D): `Q'` a genuine exact-rational ordered setoid with proved field
  laws; `CReal` a genuine Bishop regular-Cauchy real with PROVED arithmetic, abs+triangle,
  completeness (`convergesTo_unique`), `sqrt`/`cbrt` defining identities, `exp` with its functional
  equation. Theorems built on the on-path `CReal` `Equiv`/`leRat`/`geRat` API **mean what they say**.
  Two honest caveats (purity, not soundness): `CReal`'s primitive `le` is non-transitive by design
  (worked around via `Equiv`/`leRat`/`geRat`); the transitive `RegularCReal` lacks `mul`/`abs` and is
  off the gap path; `CReal.cauchy` modulus is Prop-level (Rule-8 Type-level refactor still pending).

## The Clay-requirements ledger

Clay/Jaffe–Witten: for every compact simple `G`, **(R1)** construct a complete 4D quantum YM theory
(OS/Wightman axioms → reconstruction), **(R2)** non-trivial, **(R3)** mass gap `Δ>0`.

### R3 — the mass gap
- **PROVED, unconditional, but modest:** (i) the rational data `(999/1000)² ≤ 9991/10000`, `999/1000>0`
  (no spectral meaning on its own); (ii) a **finite-volume, finite-dimensional located spectral gap on
  a hand-built toy transfer model** (`LocatedReconstruction.gappedLocated`, `sep=1/2`): located + strict
  + geometric clustering `G(n)≤G(0)·sep^n` — genuine inhabitation of the located-gap API, but the model
  is constructed by hand, **not derived from Yang–Mills**.
- **CONDITIONAL headlines:** `mass_gap_SU2`, `mass_gap_simple_group` take `OSReconstruction` +
  `OSAxiomBundle` as **hypotheses** and discharge the gap conjunct by projecting `rec.hasGap`. The
  continuum measure `μ_∞` is never constructed; `OSReconstruction` has **no concrete instance anywhere**.
- **Honest continuum factoring:** `constructive_YM4_gap_conditional` proves `(4 oracles) ⇒ Δ>0 + nonzero
  correlation`, with the gap `Δ = os.locatedGap.gapMargin` coming **from the OS-carrier oracle**, not
  from the matched-retune floor. Its docstring is explicit: "NOT a proof of the Clay gap."

### R1 — construction (OS axioms + reconstruction)
- **PROVED (finite-volume / fixed-spacing):** OS2 **reflection positivity** unconditionally
  (`reflectionPositiveSchwinger_holds`: `Σ e^{−t C₂(s)} c_s² ≥ 0` for all real `c`, Schur SOS; lifted
  to n-bond product), the SU(2) heat-kernel **Gram positivity** pivots (`Pivot2/Pivot3`,
  `GramReduction`), finite-volume **GNS** (Gram positivity, normalized vacuum), **self-adjointness** of
  the constructed finite transfer operator, finite **cluster decay** (OS4-as-decay).
- **STUB / ORACLE (the Clay core):** the continuum measure on ℝ⁴ (Daniell–Kolmogorov extension —
  absent), both limits applied to the *measure/field* (Λ→∞ of the state, a→0 scaling), the OS→Wightman
  reconstruction with a **positive continuum Hamiltonian** + vacuum + Stone generator (the
  `OSReconstruction` Hilbert/operator carriers are `Unit`-witness shells with four `Prop:=True` laws),
  and **O(4) Euclidean restoration** (only an identity-rotation witness; `CarrierPrecursors` concedes
  "no genuine non-trivial precursor" — the acknowledged weakest point).

### R2 — non-triviality
- **NEVER proved for a constructed object.** The predicate `IsNontrivial` is genuine, but witnessed
  only by a hand-built 2-mode toy `SpectralModel`; `ContinuumOSCarrier.nontrivial` is a genuine (non-`True`)
  Prop over **free data inside an uninhabited oracle**. No Wilson-loop / area-law continuum correlation
  is proved (`ContinuumMeasure` explicitly lists the area law as not done).

### All groups
- **GENUINE reduction to SU(2)** on the budget side: `mass_gap_simple_group` derives the σ̂-budget
  closure for all admissible compact simple `G` via `budget_closes_uniform` (monotone domination by
  SU(2), the worst case), atop the proved rep-theory (`RepTheory/SU2` Casimir 3/4; `SUNWeylData` every
  fundamental weight of every SU(N) clears 3/4, worst case i=1, universal in N — no enumeration). But it
  **transports the conditional OS interface**, not a constructed gap.

## What is genuinely PROVED (the real, unconditional, axiom-clean content)

The constructive **lattice/finite-volume side** is real mathematics: the `Q'`/`CReal` substrate;
the SU(2) Casimir gap 3/4 and the all-simple-groups Casimir floors (worst case SU(2)); **unconditional
OS2 reflection positivity** (Osterwalder–Seiler/Schur); SU(2) heat-kernel Gram positivity; finite-volume
GNS + self-adjoint finite transfer operator; finite-volume located spectral gap (API inhabited, toy
model) with geometric clustering; budget monotonicity / the all-groups reduction; one-loop `β₀>0`. Plus
this session's matched-retune machinery (cube root, `(r,d)` box form, telescoping engine, anchor, the
dominance/derivative *reductions*) — all PROVED, but feeding the conditional factoring, not a gap.

## What is OPEN (the named-obligation / oracle inventory — all uninhabited unless noted)

Critical-path oracles: `TrueRGComparison` (bond-move ↔ true 4D RG, summable error), `ContinuumOSCarrier`
(OS-reconstructed H/Ham + located continuum gap + nonzero correlation), `ContinuumLimitData` (a→0
modulus, volume-uniform cluster, RP, Euclidean/O(4) invariance), `GenuineResidualBound` (the
matched-retune per-mode bound). Below it: `BoxRatioDominance`, `BoxRatioDerivative`, `ClebschRDReindex`/
`RDFactorization`, `QuotientActiveWindowCertMatched`, `StepSumCert`, `CrossDiffNumeratorBound`,
`PartitionUpperDyadic`/`TailMomentCert`, the `AFRateModulus`/cutoff certs, and the demoted-wall residuals
(`DiffJTP`, `ThetaFamilyAssembly`, `RealThetaPerN`, `ProductDerivativeLimit`). The four `Prop:=True` OS
predicates + four `Unit`-witness carriers. **One degenerate inhabitant:** `UniformClusterBound` is
satisfied only by a constant-`sep=1/2`, zero-tail witness — type inhabited, physics not derived
(in-line comments concede this).

## Two parallel gap formulations (worth knowing)

1. `MassGap/{SU2,SimpleGroup}` — older; conditional on `OSReconstruction` (gap **injected** as
   `rec.hasGap`, `gapBound` unconstrained), all-groups reduction on the budget side.
2. `constructive_YM4_gap_conditional` (`ContinuumYMStack`) — newer; honest 4-oracle factoring. **This
   session's matched-retune work feeds the `GenuineResidualBound`/product-floor piece of THIS path**, and
   is OFF the `mass_gap_*` headline path. Even fully closing the matched-retune box inequalities discharges
   only `GenuineResidualBound`; `ContinuumOSCarrier` (= R1 reconstruction + R3 continuum gap) and
   `TrueRGComparison` + `ContinuumLimitData` remain.

## Fixable honesty blemishes (concrete, worth addressing)

1. **The Q' headline `mass_gap_SU2` is wired weaker than its name.** `HasSpectralGap rec` only asserts
   `∀i, rec.spec.lam i ≤ rec.gapBound` with `gapBound` carrying **only** `gapBound_nonneg` (no `<1`, not
   linked to `m_0`). A caller can discharge it with `gapBound=1` (no decay). FIX: add `gapBound_lt_one`
   to `OSReconstruction` (the `LocatedReconstruction` path already has it) and/or bind `m_0` to the
   margin as the CReal variant `mass_gap_SU2_creal` does via `hbind`.
2. **Four `Prop:=True` stubs** (`VacuumNormalized`, `HamiltonianNonneg`, `VacuumAnnihilated`,
   `SemigroupGenerated` in `OSReconstruction.lean`) + `Unit`-witness Hilbert/operator carriers. FIX:
   either upgrade to genuine predicates (as `OSAxioms`'s `IsOSk` were upgraded) or replace with explicit
   named hypotheses so nothing reads as content that is `True`.
3. **`UniformClusterBound` degenerate inhabitant** — the docstring's physics claim outruns the
   constant-`sep` witness. FIX: relabel the witness as the degenerate placeholder it is (the comments
   already say so; make it un-missable), or gate the "physics" claim behind the real (open) instance.
4. **Theorem names vs hypotheses** — `mass_gap_SU2`/`mass_gap_simple_group` read stronger than "gap given
   an OS reconstruction that already contains the gap." FIX: rename to `…_of_osReconstruction` /
   `…_conditional`, matching the honest `constructive_YM4_gap_conditional` convention.

## Honest distance to Clay

The genuinely-proved content is the **constructive lattice scaffolding** (substrate, Casimir floors,
unconditional OS2 reflection positivity, SU(2) Gram positivity, finite-volume GNS + located gap API,
budget reduction). Every **irreducibly-Clay** obligation — continuum measure on ℝ⁴, the two limits of
the *measure*, OS→Wightman reconstruction with a positive continuum Hamiltonian, O(4) restoration, a
non-zero continuum gauge correlation, and the continuum mass gap itself — is a named hypothesis or
(largely uninhabited) oracle. The matched-retune programme has reduced *one* of these oracles
(`GenuineResidualBound`) to two reconnaissance-confirmed-true box inequalities, but that is one leaf of
one oracle on one of the two gap paths. The formalization's value is the **precise, machine-checked,
honest map** of the distance — not its traversal.
