# Consolidation: the complete abstract scaffold and the unified R1 wall (2026-06-22)
**STATUS:** Scope/plan dated 2026-06-22; see the canonical ledgers for the outcome (docs/where-the-wall-sits-2026-06-22.md, docs/stage1-completion-ledger-2026-06-22.md, docs/stage2-progress-ledger-2026-06-22.md, docs/continuum-wall-outstanding-2026-06-22.md).

Supersedes the post-audit picture of `docs/clay-requirements-audit-2026-06-21.md` with the work done
since. Verdict unchanged at the top level — **Clay is OPEN; this is an axiom-clean conditional/abstract
scaffold, not a proof** — but the scaffold is now substantially more complete and, crucially, every
route has been driven to the SAME irreducible wall, which is now precisely named.

## Soundness (unchanged, re-confirmed)

Mathlib-free, choice-free, no `sorry`/`admit`/`axiom`/`native_decide`/`Real`; axiom-clean
(`propext`/`Quot.sound` only), ~2323 tracked theorems. The `Q'`/`CReal` substrate is a sound
constructive real foundation (incl. `sqrt`, `cbrt`, `exp`); theorems mean what they say.

## What is now genuinely PROVED (axiom-clean), beyond the 2026-06-21 audit

### Honesty-hardening (claims now match content)
- `gapBound_lt_one` added to `OSReconstruction` ⇒ `HasSpectralGap.clustering` is genuine geometric
  decay (the spectral conjunct now asserts a real gap).
- The four `Prop:=True` OS stubs replaced by carried abstract-`Prop` obligations (no `True`-as-content).
- Degenerate cluster witnesses relabeled `degenerate*ClusterBound` with banners.
- Headlines renamed `mass_gap_*_of_osReconstruction` (conditionality in the name).

### The matched-retune leaf (model-RG / `GenuineResidualBound`)
- The cubing trick: both box inequalities reduced to pure-`Q'` form (ρ/CReal/bracket/depth eliminated).
- The genuine residual is `τ²` (`α=0`, numerically confirmed); the chain receives it.
- `g_s` log-concavity found FALSE-in-general (counterexample); the `N=1` strong-coupling case + falsity
  witness banked. The derivative bound windowed (`∀k` was false in the tail).
- HONEST WALL: the box inequalities are the SHARP discrete local CLT, blocked by the absence of CReal
  integration (sharp `O(u³)` discrete asymptotics) — `RDThetaTail`/`RDThetaCentered` (Layer-1 theta
  bounds) banked, but two-sided bracketing cannot reach the `O(u³)` margins.

### The strong-coupling cluster-expansion ABSTRACT TOWER (now complete)
All proved, axiom-clean:
- **L0a** `PlaquetteActivity`: `plaqActivity w ≤ 4w³` (`w≤½`), derived from characters (fiducials
  superseded).
- **L0b** `PolymerModel`: the previously-absent combinatorial object — lattice, polymers (size,
  connectivity), the Haar `linkConstraint` (`fusesToTrivial_iff_eq`: `χ₀∈χ_a⊗χ_b ⇔ a=b`), activity.
- **L1** `KPCriterion`: the single-rep collapse PROVED (the Haar cancellation mechanism realized) +
  the KP criterion conditional on `ClusterCountBound`.
- **L2/(a)** `ClusterCount`: `ClusterCountBound` INHABITED (`K=deg²`, walk-encoding injection +
  Mathlib-free `choiceSeqs` count) ⇒ the abstract KP criterion UNCONDITIONAL.
- **L3a/(b)** `ClusteringImpliesGap`: the clustering⇒gap converse PROVED (`clustering_implies_located`,
  `sep=μ<1`) + the `UniformClusterBound.located` bridge.
- The KP limit engine, `KPIncrement`, and the `ClusterGapReduction` bridge (UniformClusterBound ⇒
  positive continuum-rate mass) were already proved.

So the cluster-expansion is now a complete genuine chain — **at the abstract/structural level**.

## The UNIFIED wall (the key consolidation finding)

Every route now bottoms out at the SAME place — the **real-object connection** = the **R1 construction**:
- **matched-retune:** sharp local CLT (no CReal integration).
- **cluster-expansion:** the abstract KP criterion sums over `animalCount`, NOT the real polymer
  enumeration (the **real-polymer reindexing** `∑_{X∋p}activity·e^{|X|}=∑_n#{size-n}(c_r)^n e^n` is
  missing); the clustering⇒gap converse is about the abstract `corr=Σw_iλ_i^n`, NOT the real Wilson
  correlator (the **`corr`↔correlator** identification is missing).
- **continuum oracles:** `TrueRGComparison` (a→0 crossover, genuinely open), `ContinuumLimitData`
  (a→0 + O(4), walls), `ContinuumOSCarrier` (OS reconstruction).

ALL of these reduce to: **construct the actual 4D SU(2) lattice gauge measure** (`μ_∞`: its
partition function, Haar integration, the polymer-expansion identity, the Wilson correlator) and the
continuum limits — i.e. **Clay R1**. The `ContinuumMeasure` inverse-limit is scaffolded but the
Daniell–Kolmogorov extension is absent; `corr`/`SpectralModel`/`animalCount` are abstract data not
tied to a constructed measure.

## Honest standing (the summit of the abstract scaffold)

The project is a **complete, genuine, axiom-clean ABSTRACT/CONDITIONAL scaffold** of the Clay proof:
the engines, bridges, OS2 reflection positivity, finite-volume GNS, the all-groups Casimir reduction,
and now the full cluster-expansion abstract tower and the clustering⇔gap equivalence are real proved
theorems. The single irreducible wall, shared by ALL routes, is the **R1 real-object construction** —
the actual 4D lattice gauge measure and the connection of the abstract structures to it. This is the
genuine Clay content (and the hardest), and it is now precisely named, not diffuse.

Clay R1 (construct the QFT): the real measure/limits — OPEN (the wall). R2 (non-triviality): no real
Wilson correlator — OPEN. R3 (gap): genuine only as the abstract spectral-datum gap + the
fixed-spacing finite-volume located gap; the continuum gap rides on R1.

Next (scoping, separately): the R1 real-measure construction — see the R1 scope doc.
