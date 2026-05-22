# AGENTS.md — Lean Constructivity Contract

This file is the contract for any agent working in the `lean/` folder. 

The rules below are **non-negotiable**. The entire point of the Lean
formalization is to enforce constructivity that prose cannot. An
agent that closes goals classically silently defeats that purpose.

---

## Rule 0: Read before writing

Before adding or modifying any Lean file, read:
1. `lean/README.md` (this folder's purpose and structure).
2. `docs/context.md` §1 (the intuitionistic gap audit — *why*
   constructivity matters here).
3. `docs/outline.md` §0.2 (the constructive law) and §0.3 (the
   no-circularity law).
4. This file in full.

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
that carry no erased computational content. If in doubt, treat their
appearance as a signal to review whether a witness has been silently
discarded.

Do **not** use `open Classical`, `by classical`, `Classical.choice`,
`Classical.dec`, `Classical.arbitrary`, or `Classical.choose` in any
file under `YMGap/` except inside clearly-marked,
quarantined-and-justified blocks (Rule 4).

If a goal seems to require classical reasoning, that is usually a sign
the *statement* is wrong for this program — it should be restated with
a constructive witness (Rule 2), not proved classically.

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

---

## Rule 7: Build and check before declaring done

A change is complete only when:

1. `lake build` succeeds (or fails only on logged `sorry`s).
2. Every new load-bearing theorem has a passing `#print axioms` check
   (Rule 1).
3. New quarantined classical uses are in `CLASSICAL_LEDGER.md`
   (Rule 4).
4. New holes are in `SORRY_LEDGER.md` (Rule 6).
5. The corresponding `work_plan.md` milestone status is updated if a
   Lean deliverable was its blocker.

---

## Summary

The folder exists to make one promise checkable: *the constructive
steps are actually constructive.* Classical Lean makes that promise
trivial to break by accident. These rules — sigma-not-exists,
constructive reals, the axiom gate, quarantine, honest holes — are how
the promise stays intact. When a rule and a quick proof conflict,
the rule wins.