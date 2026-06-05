# Lean Formalization

This folder holds the Lean 4 formalization of the constructive
mathematical steps of the Yang–Mills mass gap program, instantiated
per gauge group [SU(2), SU(3), ...].

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
   erase computational content.
2. Existence is stated using `Σ` (sigma types) / constructive
   existence, not `∃` (`Exists`), wherever a witness is required.
   `∃` is permitted only for genuinely propositional side conditions
   that carry no computational content.
3. Real numbers and moduli use a constructive real implementation
   (see `Constructive/Reals.lean`) with explicit Cauchy moduli, not
   Mathlib's `ℝ` (which is classical via Cauchy-sequence quotients
   plus choice for completeness).
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

---

## Folder structure

```
lean/
├── README.md                  # This file.
├── AGENTS.md                  # Constructivity contract — read first.
├── lakefile.toml              # Lake build configuration.
├── lean-toolchain             # Pinned Lean version.
├── YMGap.lean                 # Root import aggregator.
└── YMGap/
    ├── Constructive/          # Constructivity infrastructure (group-independent)
    │   ├── Reals.lean         # Constructive reals with explicit moduli.
    │   ├── Modulus.lean       # Modulus-of-convergence machinery.
    │   ├── Witness.lean       # Σ-based existence-with-witness combinators.
    │   └── AxiomCheck.lean    # Helpers/macros for #print axioms gating.
    ├── RepTheory/             # Per-group representation data
    │   ├── SU2.lean           # SU(2) irreps, Casimirs, characters.
    │   ├── SU3.lean           # SU(3) (planned).
    │   └── Generic.lean       # Compact-simple-G interface the groups satisfy.
    ├── HeatKernel/            # Heat-kernel measure and tail estimates
    │   ├── Kernel.lean        # K_t(g) = Σ d_λ χ_λ(g) e^{-t C_2(λ)}.
    │   ├── Normalization.lean # t ↔ g conversion, documented choices.
    │   └── TailEstimate.lean  # Single-plaquette buffer-shell bound.
    ├── Sheaf/                 # The bound-witness sheaf framework
    │   ├── Site.lean          # The Grothendieck site over Ω_k.
    │   ├── BoundWitness.lean  # 𝒜_k as a flabby (ℝ≥0, ≤)-valued presheaf.
    │   ├── Summability.lean   # 𝒮_k: Kotecký–Preiss certificates.
    │   └── Gluing.lean        # Domination gluing + summability side condition.
    ├── RG/                    # Renormalization-group induction
    │   ├── InductiveState.lean# The package ℐ_k.
    │   ├── BlockSpin.lean     # T_b as a site morphism; pushforward.
    │   ├── TwoCell.lean       # The degradation 2-cell Θ_k and budget η_k.
    │   └── Step.lean          # The inductive step theorem.
    └── Pilot/                 # Per-group instantiations of the full step
        ├── SU2.lean           # SU(2) pilot: closes the step for a finite RG range.
        └── SU3.lean           # SU(3) (planned).
```

The dependency direction is strictly upward through this list:
`Constructive/` depends on nothing in the project; `RepTheory/`
depends on `Constructive/`; and so on up to `Pilot/`, which depends on
everything. No cycles.

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
lake exe cache get        # fetch Mathlib cache (first time)
lake build                # build everything
lake build YMGap.Pilot.SU2  # build just the SU(2) pilot
```

Every PR-equivalent change must pass `lake build` and the axiom check
described in `AGENTS.md`.

---

## Current status

Scaffolding only. No theorems closed. The first Lean target is
`YMGap/RepTheory/SU2.lean` (constructive SU(2) Casimir spectrum),
mirroring Python Milestone 1.1, because it is the smallest
self-contained constructive obligation and exercises the
`Constructive/` infrastructure end to end.