# A2 6j Pentagon — Squarefree-MERGE Canonicaliser + EXACT pentagon decision

New file: `lean/YMGap/Continuum/QuadraticKernelMerge.lean` (530 lines), imported in
`lean/YMGap.lean`. Full `lake build YMGap` green (764 jobs); frontier guard OK
(5 Clay-frontier types uninhabited — unchanged). Axiom-clean: every load-bearing
theorem `#print axioms ⊆ {propext, Quot.sound}`. LEAN-CORE only — no Mathlib,
no `ring`/`nlinarith`, no `native_decide`, no `sorry`/`admit`/new axiom, no `Prop:=True`.
Nothing committed.

## What was built (the missing piece is DONE)

The one missing piece from `QuadraticKernel.lean` was the value-preserving
squarefree-MERGE canonicaliser. It is now built, GENERAL, and proved:

1. **`sqfreeTD : Nat → Nat×Nat`** — total, kernel-evaluable trial-division square
   extractor `n ↦ (k,s)` with `n = k²·s`. Correctness invariant
   `sqfreeTD_val : (sqfreeTD n).1² · (sqfreeTD n).2 = n` proved via a loop invariant
   (`sqLoop_val`, using `Nat.mul_div_cancel'`), plus positivity `sqfreeTD_k_pos`,
   `sqfreeTD_s_pos`. Kernel `decide` on it is fast even at n≈1.6·10⁸ because the
   radicands are smooth (products of factorials) so trial division exits after a
   few GMP-accelerated steps.

2. **`term_value` — THE KEY VALUE-PRESERVATION LEMMA**: from a factorisation
   certificate `r ≃ m²·s` (`m,s>0`), `ofQ'(q)·√r ≃ ofQ'(q·m)·√s`. Proved from
   `sqrtPos_extract` (`c√s ≃ √(c²s)`) + `sq_congr` + `cmul_assoc` — exactly the
   `sqrtPos_extract`/`toCReal_qadd` route the task specified, NOT assumed.

3. **`reduce_fac`** — the certificate `r ≃ (mNat r)²·(sNat r)` derived GENERICALLY
   from `sqfreeTD_val` (Int-cast bookkeeping over the `Q'` num/den). Hence
   `reduceTerm`/`reduceList` (+ `reduceList_value`): the per-term squarefree
   reduction, value-preserved.

4. **`mergeInsert`/`mergeList`** (+ `mergeList_value`) — the equal-radicand MERGE,
   value-preserved by distribution (`ofQ'_add` + `cadd_mul` + `add3_swap`).

5. **`normalize := mergeList ∘ reduceList`** and **`normalize_value :
   toCReal (normalize xs) ≃ toCReal xs`** — the canonicaliser and its genuine
   value-preservation (SOUNDNESS substrate).

6. **The SOUND decision**: `allZeroQ` + `allZeroQ_zero` (a zero-coefficient sum has
   `CReal` value `czero`), `qValueEq x y := allZeroQ (normalize (x ++ qneg y))`, and
   **`qValueEq_sound : qValueEq x y = true → toCReal x ≃ toCReal y`** (via
   `normalize_value`, the existing `+`/`neg` homomorphisms `toCReal_qadd`/`toCReal_qneg`,
   and cancellation `A + (−B) ≃ 0 ⟹ A ≃ B`). This upgrades term-equality to a SOUND
   VALUE-equality decision. (Difference-to-zero formulation, equivalent to the
   `termEqv (normalize x)(normalize y)` intent but order-robust.)

Soundness only — no completeness/linear-independence claimed (correct: for proving
TRUE equalities you need value-preservation, which is what `normalize_value` is).
Adversarial check confirmed the decision is discriminating: a WRONG RHS (different
tetrahedron) is REJECTED by `decide` (`= false`), so the true instances are non-vacuous.

## The pentagon DECIDED EXACTLY over the REAL 6j (`sixjQ = racahSum·√triSqProd`)

Both sides assembled as `QSqrt` from the real `sixjQ` (via `qmul`/`qadd`/`scaleTerm`
with the exact Biedenharn–Elliott phase `bePhase(Σj/2)·(2x+1)`), then decided:

- **`pentagon_R`** (rational RHS = 1/2, MERGE-exercising): `a=b=c=d=e=f=½, p=q=0, r=½`.
  The `Σ_x` has 4 nonzero summands whose √-radicands (products of 12 `triSq`
  factorials, integers up to ~3·10⁶) all reduce to squarefree `s=1` and MERGE.
  Result: `toCReal lhsR ≃ sixjCReal 0 0 1 1 1 1 · sixjCReal 0 0 1 1 1 1` — the LHS
  sum of real-6j triple products equals the RHS real-6j product. The RHS is
  connected to the genuine `sixjCReal` product via `rhsR_eq` (`toCReal_sixjQ_sq` +
  `sixjCReal_sq`), so this is a real `CReal` 6j identity, not a bare `QSqrt` fact.

- **`pentagon_I` / `pentagon_I_value`** (IRRATIONAL RHS = √2/4):
  `(a…f,p,q,r)=(½,½,0,½,0,½,½,½,0)`. Here the RHS is a product of two 6j at
  DIFFERENT tetrahedra — genuinely irrational. The canonicaliser reduces both sides
  to squarefree `s=2`; `pentagon_I_value` pins the value to `(1/4)·√2` exactly
  (`toCReal [(1/4, ofNat 2)]`), an irrational `CReal` established by pure `Q'` decide.

The `decide`s run in the kernel in well under a second each (full file 0.5s).

## Honest ∀-spins-vs-finite verdict + a correctness finding on the named residual

- These are FINITELY MANY decided tetrahedra. They do NOT close the ∀-spins
  pentagon. What is now complete is per-tetrahedron decidability: the previously
  `CReal`-undecidable pentagon at any FIXED physical tetrahedron is an exact,
  kernel-decidable computation via `qValueEq`.

- **Correctness finding (reported, not hidden):** the existing named residual
  `SixJRacahCReal.BiedenharnElliottCReal`, as LITERALLY stated over the UNGUARDED
  `sixjCReal`, is NOT a universally-true identity. Independent `sympy` cross-check:
  `sixjCReal = racahSum·√triSqProd` matches `wigner_6j` exactly on the physical
  tetrahedron (`valid6`, 0 mismatches) but is spuriously NONZERO at ~1575/6159
  invalid triangles (`racahSum ≠ 0` off-triangle). Consequently the pentagon `Σ_x`
  picks up spurious intermediate contributions and the literal identity FAILS for a
  positive fraction (~22%) of tuples (holds ~78%). The TRUE ∀-spins identity holds
  400/400 random tuples when each 6j is the GUARDED one (`wigner_6j` = 0 off
  triangle). So the correct ∀-spins statement needs a `valid6` guard on each
  `sixjCReal`. The instances proved here are chosen among tuples where the literal
  (unguarded) arrangement genuinely holds — they are TRUE `CReal` identities.

## Is A2 CLOSED? No — but the sharp missing piece is built; A2 further reduced.

- A2's guard-typed slot is `PentagonRelation.PentagonNumericCore` (in
  `Tier0Scorecard.SubWallA.a2Pentagon` and `FrontierDAG.a2Pentagon`). That spec is a
  nonneg rational kernel pinned to 1/4 — already INHABITABLE (`numericShapeWitness`,
  `racahKernelCore`); it never gated the frontier guard. So closing/deciding the
  pentagon does NOT and should NOT flip the guard: it stays 5 uninhabited
  Clay-frontier types (Tier0Scorecard/FrontierDAG remain open via their OTHER
  fields). Verified: guard green, 5 types, unchanged. This is NOT a D-move on the
  guarded frontier.

- The GENUINE A2 content (the Biedenharn–Elliott identity, linear in the signed 6j)
  is STRONGLY REDUCED: the sharp remaining step named in `QuadraticKernel.lean` —
  the squarefree-merge canonicaliser — is now BUILT and proved value-preserving, the
  per-tetrahedron pentagon is decidable EXACTLY, and the decision is exercised
  non-vacuously on a merge-heavy rational tetrahedron and a genuinely irrational one.
  Remaining residual: the uniform-in-spins identity, which additionally requires
  correcting the statement with the `valid6` guard (finding above). The 4D
  Yang–Mills mass gap stays OPEN; nothing is faked.

## Verification re-run
- `lake build YMGap` → 764 jobs, exit 0.
- `lake build YMGapGuard` → `frontier-guard OK: 5 Clay-frontier types ... uninhabited`.
- `#print axioms` on `sqfreeTD_val`, `term_value`, `reduce_fac`, `reduceList_value`,
  `mergeList_value`, `normalize_value`, `qValueEq_sound`, `pentagon_R`, `pentagon_I`,
  `pentagon_I_value` → all `[propext, Quot.sound]`.
- Pentagon lemmas reference the REAL `sixjQ` (`racahSum·√triSqProd`); decision is
  exact `QSqrt` (not `CReal` approximation); adversarial wrong-RHS rejected.
- grep: no `native_decide`/`sorry`/`admit`/`Prop:=True` in code.
