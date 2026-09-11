# AGENTS.md — Lean Constructivity Contract

This file is the contract for any agent working in the `lean/` folder. 

The rules below are **non-negotiable**. The entire point of the Lean
formalization is to enforce constructivity that prose cannot. An
agent that closes goals classically silently defeats that purpose.

## Machine-safety precondition

Uncapped Lean checks have exhausted this host and crashed the MacBook Pro twice.
No rule below authorizes an unsafe verification run.

- Never run bare `lake build` or `lake env lean YMGap.lean`. Never run Lean
  builds concurrently with each other or with a broad test suite.
- Static inspection comes first. The default agent-initiated check is the
  smallest relevant target with one worker, launched from the repository root
  through the atomic session lock:
  `scripts/with_lean_session_lock.sh lean env LEAN_NUM_THREADS=1 lake build <Module.Target>`.
- Check for an existing GitHub runner supervisor/helper/listener/worker or
  `lean`/`lake`/`pytest` process before compiling. Do not compete with or
  kill a user-owned process.
- Never bypass the lock wrapper or a locked repository Make target.  The lock
  covers repository-managed entry points; the process check is still required
  because no project script can prevent an arbitrary bare executable.
- After Control-C, TERM, HUP, or an abrupt child failure, never remove a
  retained lock until process inspection conclusively shows that no
  GitHub runner supervisor/helper/listener/worker, Lean, Lake, or pytest
  process survives.
- A full build, audit, or guard run requires explicit user approval for that
  specific run after targeted checks pass. Use the repository Make target with
  `LEAN_JOBS=1`. This one-worker setting is a hard repository invariant on this
  host; do not raise or bypass it.
- The `-M 20480` per-worker ceiling in `lakefile.toml` is mandatory. Raising or
  bypassing it, including a solo `-M 40960` check, requires explicit user
  approval for that run.
- Stop on memory pressure, swapping, stalling, or thermal pressure. Report an
  unrun check honestly; do not call a historical green build a current check.

---

## Rule 0: Read before writing

Before adding or modifying any Lean file, read:
1. `lean/README.md` (this folder's purpose and structure).
2. `docs/context.md` §1 (the intuitionistic gap audit — *why*
   constructivity matters here).
3. `docs/outline.md` §0.2 (the constructive law) and §0.3 (the
   no-circularity law).
4. This file in full.
5. `lean/AXIOM_AUDIT.md` (the auto-maintained axiom-gate baseline your
   change must not regress) and, before touching anything under
   `YMGap/Continuum/` or `YMGap/Rubric/`, the PROVED/OPEN sections of
   the relevant scorecard docstrings (`Rubric/ClayScorecard.lean`,
   `Continuum/Tier0Scorecard.lean`,
   `Continuum/ContinuumFrontierScorecard.lean`) — they define which
   obligations are genuinely open (Rule 9).

### Rule 0a: Crash-safe Lean execution

Machine stability is part of proof correctness. The 2026-08-02 full audit ran
three Lean workers, each permitted 32 GiB, on a 64 GiB Mac. macOS reached 63
swapfiles and 100% of its compressor segment limit, stopped scheduling
`watchdogd` for 91 seconds, and kernel-panicked.

Consequently:

1. Never run bare `lake build` or `lake env lean`. Use `make lean-build`, one of
   the monitored Make targets, or `python3 scripts/safe_lean_build.py`.
2. The safe launcher uses two workers on the 64 GiB development Mac, preserves
   a 12 GiB OS reserve, monitors memory pressure/swap/process-tree RSS, and
   refuses a third worker. Smaller machines default to one worker.
3. Only one monitored build may exist at a time. Do not bypass its lock, memory
   checks, or process-group shutdown.
4. Build the narrowest relevant target before considering a full library
   build. Full axiom audits are integration gates, not routine substitutes for
   targeted checking.
5. If safety telemetry stops a run, allow recovery and resume with `--jobs 1`.
   Do not weaken the thresholds or immediately repeat the parallel run.
6. High memory utilization is acceptable. Compressor/swap escalation that can
   starve macOS is not. Silent output is never evidence that a build is safe.

See `docs/lean-build-safety.md` for commands, thresholds, and the postmortem.

---

## Rule 1: No classical axioms in load-bearing theorems

Every theorem that certifies a constructive obligation **must** pass
an axiom check confirming it does not depend on classical axioms.

After proving such a theorem `foo`, add:

```lean
#print axioms foo
```

The output must **not** contain:
- `Classical.choice`
- `Classical.em` / `Classical.byContradiction`
- any lemma whose own axiom set includes the above

The output **may** contain:
- `propext`
- `Quot.sound`

provided they are used only for propositional equality / quotients
that carry no erased computational content. Both are valid in HoTT
(`propext` follows from univalence for mere propositions; `Quot` is the
set-quotient higher inductive type), so they keep us inside the
MLTT/HoTT substrate (Rule 8) — but both *cost canonicity*, so prefer an
axiom-free (`#print axioms` empty) proof when one is available,
especially for `def`s and computational lemmas. If in doubt, treat their
appearance as a signal to review whether a witness has been silently
discarded.

Do **not** use `open Classical`, `by classical`, `Classical.choice`,
`Classical.dec`, `Classical.arbitrary`, or `Classical.choose` in any
file under `YMGap/` except inside clearly-marked,
quarantined-and-justified blocks (Rule 4).

If a goal seems to require classical reasoning, that is usually a sign
the *statement* is wrong for this program — it should be restated with
a constructive witness (Rule 2), not proved classically.

**`noncomputable` addendum.** A `noncomputable` marker is a canonicity
cost and gets the same scrutiny as `propext`/`Quot.sound`: every
`noncomputable` declaration carries a docstring classifying it as (a)
a constructive extraction hidden behind a Σ projection, (b) a
convenience definition awaiting a computable replacement, or (c) a
non-load-bearing helper — and appears in the `noncomputable` ledger
section of the audit (see `work_plan.md` Milestone 11.0). An
unclassified `noncomputable` in a load-bearing module is a review
blocker.

---

## Rule 2: Existence means a witness

When a claim requires a witness — and in this program, every existence
claim in the constructive law does — formalize it with `Σ` (sigma) /
constructive existence, returning the witnessing data:

```lean
-- WRONG for a witness-bearing claim:
theorem overlap_bounded : ∃ C : CReal, μ ≤ C * boundExpr := ...

-- RIGHT: return the constant as data.
def overlapBound : Σ' C : CReal, μ ≤ C * boundExpr := ...
-- or a structure carrying (C, κ, β, proof).
```

`∃` / `Exists` is permitted **only** for genuinely propositional side
conditions with no computational content (e.g. "this index set is
nonempty" used purely to discharge a hypothesis, never to produce a
value that later code depends on).

Estimates return their constants. A Kotecký–Preiss certificate is a
structure carrying `(ρ, K)` and the summability proof, never a bare
`∃ ρ K, ...`.

---

## Rule 3: Reals and moduli are constructive

Do **not** use Mathlib's `ℝ` for any quantity that participates in a
modulus, bound, or rate. Mathlib's `ℝ` is built from Cauchy-sequence
quotients and its completeness uses choice; equality on it is not
decidable.

Use the project's constructive reals in `YMGap/Constructive/Reals.lean`,
which carry an explicit modulus of convergence. Every limit, bound,
and rate is accompanied by its modulus as data. "Converges" without a
modulus is not a usable statement here.

Rational constants (Casimirs like $C_2(1/2) = 3/4$, dimensions, the
$\beta$-function coefficient $11/3 \cdot C_2(\mathrm{adj})$) should be
exact `ℚ` where possible and only embedded into `CReal` at the point
of use.

---

## Rule 4: Quarantining unavoidable classical input

Sometimes a needed Mathlib lemma is classical but its *use* is
constructively harmless (e.g. it proves a decidable proposition whose
decision you could in principle compute). Such uses must be:

1. Placed in a file under `YMGap/Classical/` (create it if needed),
   never inline in a constructive module.
2. Marked with a docstring beginning `CLASSICAL INPUT:` that states
   exactly which classical axiom is used and why the use does not
   erase a required witness.
3. Re-exported through a constructive interface that *re-proves or
   re-packages* the result with an explicit witness, so downstream
   constructive code never sees the classical axiom.
4. Logged in `lean/CLASSICAL_LEDGER.md` with one line per quarantined
   use.

If you cannot satisfy (3) — i.e. the witness genuinely cannot be
recovered — then the claim is not constructive and **must not** be
presented as discharging a constructive obligation. Flag it instead
(Rule 6).

---

## Rule 5: Mirror, don't outrun, the rest of the repo

The Lean formalization tracks the Python/LaTeX milestones in
`work_plan.md`. For a given milestone:

- The Lean obligation is to certify the **constructivity-critical**
  existence claims, not to formalize every line.
- Use the explicit constants computed in `computations/` as inputs;
  do not re-derive them numerically in Lean.
- A Lean file should not claim to certify a step whose constants the
  Python pilot has not yet produced. If you are ahead of
  `computations/`, formalize the *statement* and leave the witness as
  a clearly-marked `sorry` (Rule 6), do not invent constants.

Per-phase Lean targets:

| Phase | Constructivity-critical Lean obligation |
|---|---|
| 1 (rep theory) | SU(2) Casimir spectrum and characters as decidable/computable data. |
| 1 (heat kernel) | Single-plaquette tail bound returns $(\kappa, \beta, C)$ as witnesses. |
| 2 (sheaf) | $\mathcal{A}_k$ flabbiness and domination gluing are constructive. |
| 2 (induction) | $\mathcal{I}_k$ validation is decidable; step signature typechecks. |
| 3 (closure) | The three KP certificates are witness-bearing structures; the $\eta_k$ budget sum is a constructive inequality. |
| 7–9 (continuum / OS / mass gap) | Finite-volume functionals, partition positivity, the KP increment engine, limits, and the GNS construction carry explicit `Q'`/`CReal` moduli as data; every genuinely open analytic input is a NAMED `Type`-level field (Rule 6a), never `Prop := True` or a `Unit` witness. |
| 10–11 (uniform groups / frontier) | Per-group data (`WeylDimData`, `AxisFactorBound`, …) are decidable/computable; frontier bundles (`Tier0Scorecard`, `ClayTarget`, `UniformSpacingFloor`, …) obey Rule 9. |
| rubric (all phases) | Every scorecard MET clause is discharged by a real, cited theorem about a specific YM object of this library; transcribed predicates are faithful and non-vacuous. |

---

## Rule 6: Honest holes

An incomplete proof uses `sorry` and is logged. Never disguise a hole.

- Every `sorry` carries a comment: `-- SORRY[milestone]: <what remains>`.
- Every `sorry` is listed in `lean/SORRY_LEDGER.md` with milestone,
  file, and the obligation it stands for.
- A `sorry` standing for a *constructive* obligation must never be
  closed later by a classical proof without explicit sign-off recorded
  in the ledger. Closing a constructive hole classically is the one
  failure mode this whole folder exists to prevent.

Do not invent lemmas, constants, or citations to make a `sorry` go
away. A correct `sorry` is infinitely better than an incorrect proof.

### Rule 6a: The named-hypothesis pattern (the sanctioned alternative to `sorry`)

When a genuinely open *analytic* input must be consumed by otherwise-
complete constructive machinery, the established pattern (used by
`domGlue_preserves_KP`, `eta_dominated`, `KPIncrementData`,
`weighted_pos`, `SpectralMarginInput`, and the scorecard bundles) is:

1. Carry the input as an **explicit, named structure field or
   argument**, `Type`-level where it bears data (Rule 8.3), with a
   docstring stating exactly what it asserts and its literature
   anchor. The surrounding modules then contain **zero**
   `sorry`/`sorryAx` and remain axiom-clean *given* the field.
2. Never smuggle the conclusion into the hypothesis: the field must be
   a genuine input (the theorem must be false for arbitrary data in
   its place — cf. the `KPIncrementData` smallness note), and it must
   not be trivially inhabitable.
3. Log it: named-hypothesis obligations are tracked in
   `SORRY_LEDGER.md` entries (as the closed-machinery/open-input
   records already are) and surfaced in the relevant scorecard's OPEN
   list.
4. Discharging the field later obeys the same signs-off as closing a
   constructive `sorry`: a classical discharge requires Rule 4
   quarantine + explicit ledger sign-off, never a silent closure.
5. When partial progress *reduces* a named field (e.g. an opaque
   scalar replaced by structured per-group data, or one leg of three
   proved), the residue must be a **strictly smaller named input** —
   never a regression to the opaque original, and never a hidden
   re-assumption of what was proved.

---

## Rule 7: Targeted, resource-capped build and check before declaring done

A change is complete only when the proportionate verification below succeeds.
Verification is targeted-first and is always subject to the machine-safety
precondition above:

1. `make lean-build` (the monitored launcher) succeeds, or the explicitly
   reported verification boundary is recorded when a safety cutoff prevents a
   full build. Never bypass the cutoff to satisfy this item.
2. Every new load-bearing theorem has a passing `#print axioms` check
   (Rule 1).
3. New quarantined classical uses are in `CLASSICAL_LEDGER.md`
   (Rule 4).
4. New holes are in `SORRY_LEDGER.md` (Rule 6).
5. The corresponding `work_plan.md` milestone status is updated if a
   Lean deliverable was its blocker.
6. If a full build/audit/guard was not run because it was unnecessary or unsafe,
   the handoff says so and does not imply current-session full-tree verification.

---

## Rule 8: Stay inside MLTT / HoTT — the computational substrate

Lean is the Calculus of Inductive Constructions, an *extension* of
Martin-Löf Type Theory. Because this proof's value is its computational
content, everything we introduce going forward **must be valid in MLTT
and its homotopy-type-theory (HoTT) extension**, and should preserve
**canonicity** (closed terms compute) wherever possible. Concretely:

1. **Only `propext` and `Quot.sound` as axioms — nothing else (Rule 1).**
   Both are HoTT-valid (`propext` = univalence for mere propositions;
   `Quot` = the set-quotient HIT). `Classical.choice` / LEM are *not*
   valid in MLTT/HoTT — they are banned, not merely discouraged. Both
   permitted axioms still cost canonicity: prefer an axiom-free proof.

2. **No `native_decide`.** It discharges goals via `Lean.ofReduceBool`
   (trusting the compiler), which is neither a type-theoretic reduction
   nor MLTT/HoTT-valid. Use `decide` (kernel computation = MLTT
   canonicity) or an explicit proof.

3. **Content-bearing witnesses live in `Type`, not `Prop` (this sharpens
   Rules 2–3).** A `Prop`-level `∃` is a *valid proposition* in
   MLTT/HoTT, but Lean's proof-irrelevant `Prop` forbids large
   elimination, so a modulus / rate / bound hidden in `∃` cannot be
   recovered or computed. In MLTT the same datum as `Σ` keeps the
   witness with a working projection, and canonicity reduces a closed
   proof to an actual value. Therefore every **modulus of convergence,
   rate, or constant a later step consumes** must be carried as
   `Type`-level data (`Σ`, a `Type`-valued structure field, or a
   function `ε ↦ N`), never a `Prop` `∃`. When you must fill a legacy
   `Prop` `∃` field, build the witness as a named `Type`-level function
   first and apply it, so the computational content exists even if the
   wrapper erases it. (The `cauchy` field of `Constructive/Reals.lean`
   is exactly such a legacy `Prop` `∃`; new modulus work carries the
   modulus as data and a `Type`-level-modulus refactor of `CReal` is the
   standing direction.)

4. **Prefer predicative / setoid formulations where natural.** Plain
   MLTT is predicative and quotient-free (it uses setoids); `Q'` with
   `eqv` already *is* a setoid, so reason in the setoid rather than
   reaching for `Quot` when that avoids a `Quot.sound` dependence.
   Essential reliance on `Prop` impredicativity in the analytic core
   (`Q'`, `CReal`, the series) should be avoided; in the
   categorical/sheaf scaffolding it is tolerated but not extended.

The test for any new definition or lemma: *would it typecheck and
compute in MLTT (or HoTT, for `propext` / quotients)?* If it needs LEM,
choice, or `native_decide`, the answer is no — restate it (Rule 1) or
carry the missing witness as data (Rules 2, 8.3).

---

## Rule 9: Frontier honesty — scorecards and uninhabited bundles

The library now carries machine-checked *enumerations of what remains
open* (`Rubric/ClayScorecard.ClayTarget`, `Continuum/Tier0Scorecard`,
`UniformSpacingFloor`, `SpectralMarginInput`, `SixJPentagon`,
`FourDExistence.ContinuumYMExistence`, and successors). These bundles
are **deliberately uninhabited**: producing an inhabitant without
`sorry`/`axiom`/vacuity *is* the open Clay problem (or a named part of
it). They are the highest-stakes surface in the repository, so:

1. **Never inhabit a frontier bundle with a vacuous or degenerate
   term.** `Prop := True` laws, `Unit` witnesses, trivially-satisfiable
   weakenings of a field's type, or surrogate objects that inhabit the
   letter but not the content (cf. the `racahRP` permutation surrogate,
   which is *documented* as insufficient for the pentagon) do not close
   an atom. If a surrogate is useful, record it as a strictly-weaker
   named object with its insufficiency stated, exactly as
   `PentagonRelation.lean` does.
2. **Do not weaken a frontier type to make it inhabitable.** Any change
   to the *statement* of a frontier field (its type, its guards, its
   quantifiers) requires the same explicit sign-off as closing a
   constructive hole classically (Rule 6), recorded in the ledger and
   the scorecard docstring, with the old statement preserved in the
   docstring for the record.
3. **Legitimately closing an atom is a two-key act.** A genuine
   inhabitant must (a) pass the Rule-1 axiom gate, (b) be sorry-free,
   (c) update the scorecard's PROVED/OPEN docstring sections in the
   same change, and (d) be recorded as a dated closure entry in
   `SORRY_LEDGER.md`. Where the CI frontier guard exists
   (`work_plan.md` Milestone 12.2), its declared frontier list is
   flipped in the same change — deliberately, by a human-reviewed
   commit, never by the proof commit alone.
4. **Scorecard docstrings are load-bearing documentation.** Their
   PROVED vs OPEN sections must match the code. If your change closes,
   reduces, or refines an atom, updating every scorecard that
   enumerates it is part of the change, not a follow-up. (Known-drift
   repair is `work_plan.md` Milestone 11.0.)
5. **Every scorecard MET clause cites its discharging theorem** — a
   real, existing declaration about a specific object of this library,
   never an existential over arbitrary models. Underclaim by default:
   the Clay Yang–Mills existence and mass gap problem is OPEN, and no
   module may state or imply otherwise while any frontier bundle lacks
   a legitimate inhabitant.
6. **Label surrogate discharges as such.** A clause whose inhabitant
   is a surrogate — a model object, a weaker proxy quantity (e.g. a
   survival-product floor standing in for the dimensionless physical
   margin `Δ_k = m_lat(a_k)/a_k`), or a char-diagonal instance
   standing in for the physical inner product — is marked
   `MET-surrogate`, never plain MET, with a pointer to the pinned
   clause that supersedes it. Surrogates are legitimate scaffolding;
   presenting one as the physical discharge is the Rule-9(1) failure
   in slow motion.
7. **The pinning principle for Clay-facing targets.** Top-level target
   structures (`ClayTargetPinned` and successors) must tie all fields
   to the SAME physical objects — the same `G`, the same continuum
   measure, the same observable algebra, the same Hamiltonian — so
   that a surrogate witness for one clause fails to *typecheck*
   against the shared parameters rather than needing a human to
   notice. Free existential "model" objects in a Clay-facing target
   are a statement bug, not a proof opportunity.
8. **Anti-proliferation.** Once the canonical frontier structure
   (`FrontierDAG`, `work_plan.md` Milestone 11.14) exists, a new
   frontier enumeration may enter the tree only together with a
   PROVED coarsening/refinement bridge to it (the `toFrontierC`
   pattern). Contributions close atoms by deleting or weakening a
   canonical field *via proof* — never by adding a parallel scorecard
   whose relationship to the canonical one is prose.

---

## Summary

The folder exists to make two promises checkable: *the constructive
steps are actually constructive*, and *the open steps are actually
open*. Classical Lean makes the first promise trivial to break by
accident; vacuous inhabitants make the second. These rules —
sigma-not-exists, constructive reals, the axiom gate, quarantine,
honest holes, the named-hypothesis pattern, the MLTT/HoTT substrate,
and frontier honesty — are how both promises stay intact. The north
star: everything typechecks and **computes** in MLTT/HoTT; witnesses
are data, not erased `Prop` content; and the scorecards never claim
more than the kernel has checked. When a rule and a quick proof
conflict, the rule wins.
