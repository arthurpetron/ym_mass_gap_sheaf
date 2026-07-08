# Decision memo — the strictest edges of Mathlib-freedom

*2026-07-08 (item 6). One-page decision on where the zero-dependency stance pays for itself and
where a middle path buys speed without weakening any claim. Decision at the bottom.*

## The situation

The `YMGap` library is **zero-Mathlib**: a from-scratch constructive substrate (`Q'` exact
rationals with `decide`-checkable order, `CReal` constructive reals, hand-built θ-functions,
`RingNormaliser`, WZ telescoping). This is philosophically coherent — everything is intuitionistic
and the axiom gate is `⊆ {propext, Quot.sound}` — and the substrate is now a **sunk, reusable
cost**. But it also means paying the maximal price at *every* step: rejecting `Rat` over
`Rat.decEq`'s axiom trace, rebuilding θ-inversion, reproving elementary inequalities that Mathlib
ships. On the *analysis* frontier (Category B), that tax is heaviest exactly where the mathematics
is hardest and where fast exploration matters most.

## The tension, stated honestly

- **Keeping zero-Mathlib** protects the deliverable's meaning: the constructive library claims
  exactly what a constructivist accepts, with a tiny trusted base. This is the product.
- **Never touching Mathlib** slows the *research* — route-scouting, adversarial refutation of dead
  ends, and quantitative estimate-hunting are all faster with a mature classical library, and none
  of that speed needs to enter the deliverable.

These do not actually conflict, because exploration and deliverable are different artifacts.

## The middle path

A **segregated classical mirror track**, firewalled from the deliverable:

- A separate Lake target / directory (`Exploration/`, its own `lakefile` target) that **may import
  Mathlib**, used ONLY for: (a) scouting whether a route closes at all before constructive
  investment; (b) adversarially *refuting* routes fast (a classical counterexample kills a route
  regardless of constructivity); (c) numerically/analytically locating the constants and lemmas
  that the constructive proof will then re-establish.
- **Hard firewall:** nothing in `Exploration/` is imported by `YMGap.*`; the frontier guard, the
  axiom audit, and the statement-hash guard run only over `YMGap.*`; a CI check fails if any
  `YMGap/` file imports `Exploration/` or Mathlib. The deliverable's trusted base is unchanged.
- **The deliverable is the constructive backport.** A result is "done" only when it lives in
  `YMGap.*` axiom-clean. The mirror is scaffolding, discarded or left clearly labeled as non-load-
  bearing.

This is exactly the project's stated methodology ("constants from Python, certification in Lean")
extended one level: *routes explored classically, certified constructively.* Python already plays
the numeric-scout role; a Mathlib mirror plays the proof-structure-scout role.

## What it does NOT change

- No `YMGap.*` claim weakens; the axiom gate and guards are untouched.
- The substrate stays the product; the mirror never ships.
- Purity where it is cheap (rationals, finite combinatorics, the guard architecture) stays pure —
  the mirror is for the *analysis* frontier where the tax is real, not for re-importing `Rat`.

## Decision

**Adopt the middle path.** Stand up an `Exploration/` track that may use Mathlib, firewalled from
`YMGap.*` by a CI import-check, used for route-scouting and adversarial refutation only; keep the
constructive backport as the sole deliverable. Deploy it first on the Category-B analysis fronts
(item 12 certified-RG truncation-error lemma; item 13/15 route adjudications), where classical
Mathlib machinery (measure theory, spectral theory, special functions) lets a route be validated
or refuted in hours instead of being constructively built only to fail. Do **not** use it to
relax any constructive obligation — a mirror proof is a *lead*, never a citation.

**Next action when adopted:** add `Exploration/` + a `make check-firewall` target (grep: no
`YMGap/` file imports `Exploration` or `Mathlib`); document the firewall in `AGENTS.md`.
