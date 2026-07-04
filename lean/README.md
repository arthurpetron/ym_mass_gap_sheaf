# Lean Formalization

This folder holds the Lean 4 formalization of the constructive
mathematical steps of the Yang–Mills mass gap program, instantiated
per gauge group [SU(2), SU(3), ...] with a uniform reduction toward
all compact simple groups.

The purpose is to make the program's **constructive law** —
"every existence claim returns an object, a witness, and a computable
modulus" (`docs/outline.md` §0.2) — *mechanically enforced* rather
than merely intended. A Lean proof that typechecks under the
discipline below is a machine-checked certificate that a given step is
genuinely constructive.

> **Read `AGENTS.md` before contributing.** It contains the
> non-negotiable constructivity rules. They are easy to violate by
> accident in Lean, because Lean and Mathlib are classical by
> default.

---

## Why Lean, given that Lean is classical

Lean 4 and Mathlib admit `Classical.choice`, excluded middle, and
non-constructive existence as axioms. Left unconstrained, Lean will
happily prove `∃ x, P x` with no extractable witness. That is exactly
what this program forbids.

We therefore work in a **constrained fragment**:

1. Every load-bearing theorem is checked with `#print axioms` to
   confirm it does **not** depend on `Classical.choice`,
   `Classical.em`, `Quot.sound`-via-choice, or `propext` used to
   erase computational content. The maintained baseline is
   `AXIOM_AUDIT.md` (auto-generated; CI fails on drift).
2. Existence is stated using `Σ` (sigma types) / constructive
   existence, not `∃` (`Exists`), wherever a witness is required.
   `∃` is permitted only for genuinely propositional side conditions
   that carry no computational content.
3. Real numbers and moduli use the project's constructive reals
   (`Constructive/Reals.lean` and the `CReal*` modules) with explicit
   Cauchy moduli, not Mathlib's `ℝ` (which is classical via
   Cauchy-sequence quotients plus choice for completeness). Exact
   rational arithmetic lives in the project's `Q'`
   (`Constructive/Rationals.lean`); Lean core's `Rat` was rejected for
   load-bearing use because `Rat.decEq` depends on `Classical.choice`.
4. Estimates return the witnessing constant, not just its existence.
   A bound `μ ≤ C · exp(...)` is formalized as a function returning
   `C` together with the proof, not as `∃ C, μ ≤ ...`.

This is the same discipline as Bishop-style constructive analysis,
mechanized. The `#print axioms` gate is the enforcement mechanism;
see `AGENTS.md`.

**Substrate: MLTT / HoTT.** Lean is the Calculus of Inductive
Constructions, an extension of Martin-Löf Type Theory. We hold ourselves
to what is valid in MLTT and its homotopy-type-theory extension: the
only permitted axioms are `propext` and `Quot.sound` (both HoTT-valid —
`propext` is univalence for mere propositions, `Quot` is the set-quotient
HIT); `Classical.choice`/LEM (invalid in MLTT/HoTT) and `native_decide`
(trusts the compiler, not a kernel reduction) are banned. Because the
proof's worth is its computational content, we prefer **canonicity**:
axiom-free, `decide`-checkable proofs, and witnesses carried as
`Type`-level data (`Σ`, functions `ε ↦ N`) rather than erased inside a
proof-irrelevant `Prop` `∃`. See `AGENTS.md` Rule 8.

**No external dependencies.** The library is Mathlib-free — the Lake
manifest has zero packages. Everything builds from Lean core
(`leanprover/lean4:v4.29.1`, pinned in `lean-toolchain`).

---

## Folder structure (as of 2026-07-03)

```
lean/
├── README.md                  # This file.
├── AGENTS.md                  # Constructivity contract — read first.
├── AXIOM_AUDIT.md             # Auto-maintained axiom-gate baseline (~3.8k tracked decls).
├── SORRY_LEDGER.md            # Every sorry, logged. Currently: library is sorry-free.
├── CLASSICAL_LEDGER.md        # Every quarantined classical input (Rule 4). Currently empty.
├── lakefile.toml              # Lake build configuration (no external packages).
├── lean-toolchain             # Pinned Lean version (v4.29.1).
├── YMGap.lean                 # Root import aggregator (annotates load-bearing vs excluded).
├── docs/                      # Lean-local design notes (KP limit, RG transport, ...).
└── YMGap/
    ├── Constructive/          # Group-independent constructive substrate (~70 modules):
    │                          #   Q' exact rationals; CReal with explicit moduli
    │                          #   (arithmetic, exp/log, sqrt/cbrt, trig, π, completion);
    │                          #   geometric/finite-sum machinery; SU(3) character-tail
    │                          #   factorization; soundness bounds.
    ├── RepTheory/             # Per-group representation data: SU2, SU3, Spin4 (+H₄
    │                          #   reflection data), CasimirData, RepData, SimpleGroup
    │                          #   (the compact-simple-G interface).
    ├── BufferShell.lean       # Single-plaquette buffer-shell tail bound (κ, β, C as data).
    ├── Sheaf/                 # Bound-witness sheaf framework: Site, BoundWitness
    │                          #   (flabby presheaf), Summability (KP certificates),
    │                          #   Gluing (domGlue_preserves_KP), PolymerDomination, SU2KP.
    ├── RG/                    # RG induction + the uniform-group reduction: BlockSpin,
    │                          #   InductiveState, SigmaHatPilot(+UV), UniformBudget,
    │                          #   character-tail majorant/antitone chain, EtaPackaging,
    │                          #   SUNWeylData / WeylDimGeneral / RankCollapse.
    ├── MassGap/               # Headline composition theorems: SU2 (mass_gap_SU2),
    │                          #   SimpleGroup (mass_gap_simple_group).
    ├── Categorical/           # Site/presheaf/2-cell scaffolding; ScaleSheaf cocycles;
    │                          #   budget functors and closure transports.
    ├── Codynamic.lean         # Codynamic transfer template (EKF ↔ YM signature port).
    ├── HigherCategorical.lean # 2-categorical RG-flow packaging.
    ├── Continuum/             # The continuum campaign (~470 modules): finite-volume
    │                          #   functionals and partition positivity (S2–S6), KP
    │                          #   increment engine, reflection positivity (OS2 via
    │                          #   Osterwalder–Seiler), OS axioms + reconstruction
    │                          #   interfaces, complete GNS Hilbert space, transfer
    │                          #   calculus, spectral gap/localization, Bakry–Émery and
    │                          #   codynamic floors, Mayer/Ursell/tree-graph reductions,
    │                          #   6j/pentagon track, O(4)/H₄ restoration groundwork,
    │                          #   AF-rate calibration, and the Tier-0 frontier files
    │                          #   (Tier0Scorecard, ContinuumFrontierScorecard,
    │                          #   FourDExistence, ...). Many `*Progress`/`*Close`
    │                          #   modules are stepwise reductions of named frontier
    │                          #   atoms — check `YMGap.lean`'s annotations and the
    │                          #   scorecard docstrings for load-bearing status.
    ├── Rubric/                # Machine-checked transcription of the Clay rubric:
    │                          #   ClayScorecard (fixed-spacing line PROVED; ClayTarget
    │                          #   deliberately uninhabited), ContinuumScorecard,
    │                          #   Loop/Reconstruction scorecards.
    ├── PolyAtlas.lean         # Expository/design scaffolding — NOT load-bearing,
    ├── ModuliAlgebra.lean     #   excluded from the default aggregator (see YMGap.lean).
    └── ...
```

The dependency direction runs upward from `Constructive/` (depends on
nothing but Lean core) through `RepTheory/`, the lattice layers
(`Sheaf/`, `RG/`, `MassGap/`), into `Continuum/` and finally the
`Rubric/` scorecards. `YMGap.lean` is annotated: it states which
modules are load-bearing and which are deliberately excluded from the
default build to keep the axiom-audit surface honest.

---

## Relationship to the rest of the repository

The Lean formalization mirrors, but does not replace, the Python
`computations/` and the LaTeX `formal/`:

| Concern | Python `computations/` | LaTeX `formal/` | Lean `lean/` |
|---|---|---|---|
| role | compute explicit constants | state the argument for humans | machine-check constructivity |
| trust | numerical, regression-tested | peer-readable | kernel-verified |
| output | the numbers $(\kappa, \beta, C, \rho, K, \ldots)$ | the prose proof | the certified theorem |

The intended workflow per milestone:

1. `computations/` produces the explicit constants and a numerical
   sanity check.
2. `formal/` states the argument in prose with those constants.
3. `lean/` certifies that the argument's existence claims are
   constructive, using the constants as inputs.

A milestone's Lean obligation is **not** "formalize everything" — it
is "formalize the *constructivity-critical* existence claims," i.e.
the ones where a classical proof would be unacceptable. The
`AGENTS.md` file lists which claims those are per phase.

---

## Building

```sh
lake build                 # build everything (no external packages to fetch)
lake build YMGap.MassGap.SU2                    # just the SU(2) headline chain
lake build YMGap.Continuum.Tier0Scorecard       # just the frontier scorecard
lake build YMGap.PolyAtlas YMGap.ModuliAlgebra  # the excluded expository modules
```

Every PR-equivalent change must pass `lake build` and the axiom check
described in `AGENTS.md` (`make lean-audit` at the repo root; refresh
the baseline with `make lean-audit-update` only for deliberate,
reviewed changes).

---

## Current status (2026-07-03)

**Ledger state.** The `YMGap` library builds sorry-free (`lake build`
reports zero `declaration uses 'sorry'`; see `SORRY_LEDGER.md`, whose
remaining entries are closure records and named-hypothesis
bookkeeping, not open holes). `AXIOM_AUDIT.md` tracks ~3,758
declarations, axiom-gated to `∅` / `[propext]` /
`[propext, Quot.sound]` — no `Classical.*`, no `sorryAx`, no
`native_decide`. `CLASSICAL_LEDGER.md` has zero entries (see the
Minlos caveat below).

**Proved — the fixed-spacing Clay line.**
`Rubric.ClayScorecard.clay_fixed_spacing_met` genuinely inhabits every
fixed-lattice-spacing clause of the transcribed Clay rubric, each
discharged by a concrete named theorem about a specific YM object:
positive located spectral gap of the reconstructed transfer operator,
geometric clustering of the real Wilson connected correlator,
nontriviality, OS2 reflection positivity (via the Osterwalder–Seiler
diagonalization `ReflectionPositivity.reflSchwinger_nonneg`, which
retired the previous P_N/product-form walls from the critical path),
and infinite-volume mass positivity. Supporting closed work includes
the constructive-reals substrate, the SU(2)/SU(3) KP-certificate
derivations, the S2–S6 finite/infinite-volume functional stages
(partition positivity, reweighted state, KP increment engine, limit
with modulus), the complete constructive GNS Hilbert space
(`GNSComplete`), and the uniform-group reduction
(`mass_gap_simple_group` via the proven character-tail majorant chain,
with SU(2)/SU(3) discharged end-to-end).

**Deliberately open — the machine-checked frontier.** The continuum
(`a → 0`) Clay problem is carried as *uninhabited* bundles, never
faked, in **two complementary enumerations** whose unification is
planned (`work_plan.md` Milestone 11.14). On the measure/RG side,
`Continuum.Tier0Scorecard` enumerates: Sub-wall A (loopy geometry:
(T′) tree-graph, (D1) Mayer–Ursell bridge, (D2) separation metric,
(A2) 6j pentagon), Sub-wall B (Balaban RG: the `SpectralMarginInput`
atoms `hlocalize` / `hbridge` / `hadd`), and the orthogonal
`CitedMinlosLift` (σ-additive continuum measure — note: this
cited-classical input is not yet processed through the Rule-4
quarantine, hence the empty classical ledger currently *understates*
the continuum chain's classical content; resolving this is
`work_plan.md` Milestone 11.9). On the operator/OS side,
`Rubric.ReconstructionScorecardFinal` names five open tokens:
`OpenNode1FiniteSMargin`, `OpenTrueMargin` (the genuine dimensionless
physical margin `Δ_k = m_lat(a_k)/a_k`, distinct from the proved
survival-product *surrogate* in the green line — see AGENTS.md
Rule 9(6)), `OpenPhysicalWilsonBridge`, `OpenBoundedHamiltonian`, and
`OpenContinuumMinlos`. `ClayScorecard.ClayTarget` additionally names
O(4) restoration, coupling-uniformity, gauge content, asymptotic
freedom, and nontriviality (`Continuum/FourDExistence.lean`); the
Jaffe–Witten local-field/stress-tensor/OPE layer is currently only
two bare `Prop` fields there and is scoped as Milestone 11.17.
`ContinuumFrontierScorecard` proves that the codynamic, curvature, and
OS-reconstruction continuum routes all converge on the single
uninhabited scalar `UniformSpacingFloor`.

**Per-atom partial progress** (the scorecard docstrings may lag these;
Milestone 11.0 re-syncs them): (D2) has a sound, non-tight L¹
inhabitant (`SepLatticeZ4Close.SepLatticeZ4_witness`); (T′) is reduced
to three named legs, of which only the Penrose sign-domination is new
mathematics (`TreeGraphBoundProgress`, with the (P) leg under further
active reduction in `PenroseDomInduction`); the pentagon track has the
Level-1/Level-2 analysis and a refutation of the permutation surrogate
(`PentagonRelation`); `hbridge` has its wiring lemma
(`PinnedBridgeProgress.edgeShift_le_gradedDefect`); and the δ-loop
capstone (`DeltaFrontierLedger`) reduces the bond-moving obstruction to
the single vacuum-normalized bulk-shift residual `bulkCtrl` (= the
`hlocalize` content, open for `p ≥ 2`). Hygiene note: the library
carries exactly 9 `noncomputable` declarations (in `NormExcitedDrift`,
`DominantModeRecursion`, `UniformCouplingFromAF`), pending the
classification ledger required by the AGENTS.md Rule 1 addendum.

**Not claimed.** No inhabitant of `ClayTarget`, `Tier0Scorecard`, or
`UniformSpacingFloor` exists in this library. The Clay Yang–Mills
existence and mass gap problem is OPEN; what is machine-checked is the
fixed-spacing closure and the reduction of the remainder to the named
atoms above. The current campaign against those atoms is
`work_plan.md` Phase 11 (frontier mathematics) and Phase 12
(compliance, publication, hygiene).

---
