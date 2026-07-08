# Constructive reflective ring normaliser over Q' — DELIVERED

**File:** `lean/YMGap/Continuum/RingNormaliser.lean` (new, ~640 lines), imported in
`lean/YMGap.lean` after `RacahDougallWZ`.

## Verdict (headline)

The constructive ring normaliser is **BUILT, SOUND, and DEMONSTRATED** on a real
multivariate polynomial identity (the degree-2 Chu–Vandermonde convolution — the
"Vandermonde/Saalschütz convolution layer" flagged as *absent* in
`BiedenharnElliottGeneral`). It is Lean-core only: no Mathlib `ring`/`nlinarith`,
no `native_decide`, no `Real`/`Classical`. The soundness core `normalize_eval`
is a **genuine structural induction** on the `Q'` ring axioms — not assumed. All
load-bearing theorems are axiom-gated (`propext`/`Quot.sound`); the `decide`
step depends on **no axioms at all**.

## What was built (the reflection pipeline)

1. **`PolyExpr`** — reflective syntax as DATA: `const : Int`, `var : Nat`,
   `add`, `mul`, `neg`, `pow : PolyExpr → Nat`.
2. **`eval ρ : PolyExpr → Q'`** — the evaluation homomorphism into `Q'` at an
   environment `ρ : Nat → Q'` (integer constants via `Q'.ofInt`; powers via the
   internal fold `qpow`).
3. **`NormalPoly = List (List Nat × Int)`** — canonical form: sorted,
   like-terms-combined, zero-free list of `(exponent-vector, coefficient)`.
   Monomials are trailing-zero-trimmed exponent vectors ordered by a strict lex
   order (`monoCmp`, with `monoCmp_eq : monoCmp m m' = .eq → m = m'` proved).
   `DecidableEq` is structural list equality.
   - Operations: `monoMul` (component-wise exponent add with padding), `rawNeg`,
     `scaleTerm`, `rawMul` (distribute), `rawPow`; canonicalisation via
     `insertTerm` + `canon` (insertion sort with like-term merging / zero-drop).
4. **`normalize e := canon (rawNormalize e)`**.

## The soundness theorem (the load-bearing core — genuinely proved)

`normalize_eval (ρ) (e) : (eval ρ e).eqv (evalRaw ρ (normalize e))`

Proved by composing two theorems, each a real induction using ONLY the `Q'`
ring-axiom `eqv`-lemmas from `RationalsMul.lean`
(`mul_comm_eqv`, `mul_assoc_eqv`, `mul_add_eqv`, `add_assoc_eqv`,
`mul_eqv_congr_*`, `add_eqv_congr_*`, `neg_*`, …):

- `eval_rawNormalize : (eval ρ e).eqv (evalRaw ρ (rawNormalize e))` — structural
  induction on `PolyExpr`, resting on:
  - `evalMono_monoMul` — **monomial multiplication is a `Q'` homomorphism**
    (`evalMono ρ (monoMul a b) ≃ evalMono ρ a * evalMono ρ b`), the crux lemma,
    proved by double induction using `qpow_add` and a 4-factor rearrangement
    `q_mul4_swap : (a*b)*(c*d) ≃ (a*c)*(b*d)`;
  - `evalRaw_append`, `evalRaw_rawNeg`, `evalRaw_scaleTerm`, `evalRaw_rawMul`,
    `evalRaw_rawPow` — each an induction on list/exponent structure.
- `evalRaw_canon : (evalRaw ρ (canon p)).eqv (evalRaw ρ p)` — via
  `evalRaw_insertTerm` (the three `monoCmp` cases: prepend / combine-or-drop /
  recurse), which uses `ofInt_add`, `q_add_mul`, and `q_zero_mul`.

**Nothing in this chain is `sorry`/`axiom`/assumed.** Every step is a proved
`Q'.eqv` congruence.

## The decision procedure (SOUND)

`poly_identity_of_normal_eq (e₁ e₂) (h : normalize e₁ = normalize e₂) (ρ) :
  (eval ρ e₁).eqv (eval ρ e₂)`

If the two normal forms are structurally equal, `evalRaw` on them is literally
the same `Q'` value, so soundness + `eqv_trans`/`eqv_symm` gives the identity for
**every** environment `ρ`. Soundness only (proves true identities); completeness
is not claimed.

## The demonstrated multivariate identity (the Racah unlock)

Degree-2 Chu–Vandermonde convolution, cleared of denominators:

  **`n(n−1) + 2·m·n + m(m−1) = (m+n)(m+n−1)`  for all `m, n : Q'`.**

This is the `k = 2` member of the Vandermonde/Saalschütz convolution family named
as *absent* in `BiedenharnElliottGeneral` (`Σ_k C(m,k)C(n,2−k) = C(m+n,2)`).

- `vdm_normal_eq : normalize vdmLHS = normalize vdmRHS := by decide` — a genuine
  kernel computation. Both sides canonicalise to the identical non-trivial
  5-term normal form
  `[([0,1],−1), ([0,2],1), ([1],−1), ([1,1],2), ([2],1)]`
  (i.e. `−n + n² − m + 2mn + m²`), verified by `#eval` = `true`.
- `vandermonde_deg2 (m n : Q')` — the identity via `poly_identity_of_normal_eq`.
- `vandermonde_deg2_explicit (m n : Q')` — the readable `Q'`-arithmetic corollary
  `(n·(n+(-1))) + (2·m)·n + (m·(m+(-1))) ≃ (m+n)·((m+n)+(-1))`.

**Genuinely beyond `ac_rfl`/`omega` — verified adversarially:** on the underlying
`Int` polynomial identity, `ac_rfl` fails (`rfl failed`) and `omega` fails
(`could not prove the goal`) — because it is nonlinear (`m²`, `n²`, `mn`) and
requires distribution + cross-term cancellation. The normaliser proves it.

## Verification (all re-run)

- `lake build` (full project): **exit 0**, "Build completed successfully (787 jobs)".
- Guard 5 (`lake build YMGapGuard`): **PASS** —
  "frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited across YMGap.*".
- `#print axioms`:
  - `evalMono_monoMul`, `evalRaw_rawMul`, `eval_rawNormalize`, `evalRaw_canon`,
    `normalize_eval`, `poly_identity_of_normal_eq`, `vandermonde_deg2`
    → `[propext, Quot.sound]` (within the gate).
  - `vdm_normal_eq` (the `decide`) → **does not depend on any axioms**.
- No `sorry`/`admit`/new `axiom`; no `native_decide`; no `ring`/`nlinarith`;
  no `Classical.*`. (`set` was replaced by core `let`; `ring_nf` avoided.)
- MLTT Rule 8: `normalize`/`eval` are Type-level `def`s; identities are
  propositional `eqv` facts; no data hidden behind `Prop`-`∃`.

## Residual (honest scope)

- **Coefficients are `Int`** (embedded into `Q'` via `ofInt`). This decides
  polynomial identities with integer coefficients — equivalently rational
  identities **after clearing denominators**, which is exactly what the WZ
  cross-multiplication / certificate step always produces. **Genuine
  rational-function (division) identities**, and coefficients needing
  `gcd`-normalisation of `Q'` num/den, are **NOT** handled and are the named
  residual (would need a `Q'.reduce` + a normalised-coefficient layer).
- **Completeness is not proved** (only soundness). Canonicalisation makes
  completeness hold in practice — the demonstration depends on it computationally
  and the kernel confirms it — but there is no theorem "equal polynomials ⇒ equal
  normal forms". Soundness is all that is needed for a *sound* decision procedure.
- The normaliser is now available infrastructure for the WZ route: any Racah/WZ
  certificate step whose verification reduces (after cross-multiplication) to a
  multivariate polynomial identity over `ℤ` can be discharged by
  reflect → `normalize` → `decide` → `poly_identity_of_normal_eq`, replacing the
  hand-proved algebra those steps currently require.

## Next front (per the loop)

The delivered normaliser removes the "no Vandermonde/Saalschütz convolution
layer" obstruction at the *polynomial-identity* level. The remaining Racah
residual (`BEDougallMultiSum = BEDougallCore` in `RacahDougallWZ.lean`) is a
**multi-sum** whose closure needs a Zeilberger/creative-telescoping recurrence
over the three inner Racah `t`-sums — the normaliser now discharges the per-step
polynomial certificates that recurrence generates, so the live sub-target is
assembling the recurrence itself on top of `int_telescope` + this normaliser.
