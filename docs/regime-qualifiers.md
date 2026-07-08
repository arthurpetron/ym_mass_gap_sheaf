# External framing — regime qualifiers and what is genuinely novel

*Generated 2026-07-08 (item 8 of the strategic roadmap). This is the framing contract for every
external artifact: paper, abstract, talk, README. State the regime qualifiers yourself, before a
referee states them for you; and let the claims be exactly as large as the kernel has checked —
no larger. Underclaim by policy (cf. `reference_clay_open_boundary_ledger`).*

---

## The qualifier that must appear next to every gap claim

> **fixed lattice spacing, strong-coupling regime, at the specific operating point `w` (the pilot
> couplings pinned in `BudgetConstants.lean`).**

Any sentence that says "mass gap" without these three qualifiers is an overclaim. The three are
independent and each is load-bearing:

1. **Fixed spacing.** What is machine-checked is a gap of the fixed-spacing lattice theory. The
   continuum limit `a→0` (`ClayContinuumExistence`) is the open Clay content — the 2D adequacy
   test (this session) confirmed `ClayContinuumExistence` is correctly the *only* substantive
   obstruction remaining inside `ClayTarget`, and it does not compose trivially. Say "fixed
   spacing" every time.
2. **Strong coupling.** The proved regime is strong-coupling (small-`β`), where the transfer
   operator's spectral gap is accessible (Osterwalder–Seiler / Shen–Zhu–Zhu). The crossover to
   weak coupling through asymptotic freedom is `singleStep` — open.
3. **Specific `w`.** The pilot operating point is a specific coupling (`m₀=999/1000`,
   `σ̂=9991/10000`, `η_max` per `BudgetConstants`), not a uniform-in-`w` statement. The uniform
   worst-case reduction (SU(2)) is real but is a *group*-uniformity, not a *coupling*-uniformity.

**The Clay problem remains OPEN.** State it plainly in the abstract, not just the conclusion.

---

## What IS genuinely novel — sell these

The physics claim is deliberately modest. The genuinely novel, defensible contributions are
methodological and architectural, and they are real:

1. **Machine-checked constructive mechanization.** A large, axiom-clean (`⊆ {propext, Quot.sound}`,
   no `sorryAx`/`Classical`/`native_decide`) Lean development of lattice gauge theory in an
   intuitionistic substrate. 7596 tracked theorems, statement- and axiom-gated in CI. This is the
   deliverable, and it is genuine.
2. **The constructive Q'/CReal substrate as a certified-arithmetic engine.** Exact rational
   arithmetic with `decide`-checkable inequalities — a reusable, sunk-cost foundation that turns
   quantitative RG estimates into machine-checkable objects (the basis for the item-12 certified-RG
   route). Reject-`Rat` purism is a deliberate cost; see the Mathlib-freedom memo for the middle
   path (classical exploration mirror, constructive backport as deliverable).
3. **The uniform-group reduction.** The mass gap for all simple groups reduced to the SU(2)
   worst case (`mass_gap_simple_group`, `RG/SUNWeylData.lean`) — one worst-case reduction, not a
   per-group enumeration. Rep-theoretically genuine.
4. **The guard architecture.** A two-layer anti-vacuity defense: the *inhabitation* guard
   (`YMGapGuard`, frontier types must stay uninhabited — catches a vacuous "closure") and the
   *statement-hash* guard (item 5, catches silent weakening of the pinned statement). Plus the
   hashed axiom-audit baseline and the anti-proliferation rule (9.8, FrontierDAG single-source).
   This architecture — making "did we accidentally cheat?" a mechanical CI check — is itself a
   contribution to how large formal-proof efforts stay honest.

The rule: **the physics claim is exactly the size of the kernel; the novelty is the method.**

---

## Concrete wording templates

- **Abstract opener:** "We give a machine-checked constructive proof, in Lean, of a mass gap for
  fixed-spacing strong-coupling lattice SU(N) Yang–Mills at a specific coupling, together with a
  reduction of the all-simple-groups case to SU(2). The continuum limit — the Clay problem —
  remains open; we make the open boundary explicit and machine-guarded."
- **Never:** "We prove the Yang–Mills mass gap." (overclaim — drops all three qualifiers.)
- **Talk slide footer:** "fixed spacing · strong coupling · specific w · continuum OPEN."
- **When asked 'is this the Clay problem?':** "No — it is the fixed-spacing strong-coupling kernel
  of it, fully mechanized, with the remaining continuum obstruction (`ClayContinuumExistence`)
  isolated, named, and guarded. The novelty is the constructive mechanization and the honesty
  architecture, not a continuum claim."

---

## Cross-references

- `reference_clay_open_boundary_ledger` — the canonical honest proved-vs-open accounting.
- `docs/frontier-burndown.md` — D=0; the honest reduction-vs-work picture.
- `docs/frontier-triage.md` — what is known-math-to-constructivize vs genuinely-new.
- The statement-hash guard (item 5) — makes the pinned statement mechanically drift-proof.
