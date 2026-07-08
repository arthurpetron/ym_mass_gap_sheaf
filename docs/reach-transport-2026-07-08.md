# ReachTransport / SpansContractLt — the (P) BFS residual: RESOLVED (with a correction)

## Headline

The "sole remaining genuine-TRUE (P) residual" — the weightless BFS walk-transport
`ReachTransport` / `SpansContractLt` — is **resolved**, but the honest resolution is a
**correction**:

* The statements **as currently written in the repo are FALSE** (they quantify over an
  arbitrary edge list `A`). Machine-refuted.
* The genuinely-TRUE statements carry the range guard `InRange n A` (every endpoint of
  `A` is `< n` — exactly the polymer/`adjGraph` regime, preserved by contraction). Both
  are now **machine-PROVED, axiom-clean**.

All new work is in `lean/YMGap/Continuum/SpansContractInRange.lean` (imported into
`YMGap.lean`). Full `lake build` green (786 jobs); frontier guard green ("frontier-guard
OK: 5 Clay-frontier types unconditionally uninhabited"); every declaration
`#print axioms ⊆ {propext, Quot.sound}`. No `sorry`, no `native_decide`, no `Classical.*`.

## The adversarial finding (why the unguarded forms are false)

The fixed-fuel BFS `reachClosure n A [0]` only saturates to true reachability when every
label of `A` is `< n`. With an out-of-range label a long detour needs **more than `n`**
passes, and the merge-created shortcut breaks the biconditional. Exhaustive + ~900k random
search located it; the minimal witness (verified in-Lean by `decide`):

```
n = 3, (a,b) = (0,1), A = [(0,3),(3,4),(2,4)]        -- guards a<b, b<n hold; labels 3,4 ≥ n
  spans 3 ((0,1)::A)            = true    (0—1, 0—3—4—2 connected)
  spans 2 (contractEdges 0 1 A) = false   (needs fuel > 2)
  at i=2:  2 ∈ reach_G = true ,  relabelV 0 1 2 = 1 ∈ reach_{G/e} = false
```

The prior docstrings claimed these "genuinely TRUE (brute-force validated over all graphs
on n ≤ 4) … NOT refutable"; that validation silently used only in-range `A`. Corrected the
`SpansContractProof.ReachTransport` docstring accordingly.

## What is PROVED (all axiom-clean `[propext, Quot.sound]`)

* **`reachTransport_inRange`** — the guarded `ReachTransport` (the BFS walk-transport core).
  For `a<b<n`, `InRange n A`, and `i<n`:
  `i ∈ reachClosure n ((a,b)::A) [0] ↔ relabelV a b i ∈ reachClosure (n-1) (contractEdges a b A) [0]`.
* **`spansContractLt_inRange`** — the guarded `SpansContractLt`:
  `spans n ((a,b)::A) = spans (n-1)(contractEdges a b A)` for `a<b<n`, `InRange n A`.
* **`treeCountContract_inRange`** — the non-loop **`treeCount`** deletion–contraction half
  of the recursor, now closed **outright** (no free hypothesis) over any in-range graph;
  it consumes exactly `spansContractLt_inRange` (per sublist, via `inRange_of_mem_sublists`),
  replacing the previously unsatisfiable-hypothesis `treeCountContractGuarded`.
* **`reachTransport_unguarded_false`**, **`spansContractLt_unguarded_false`** — the two
  refutations of the unguarded defs.
* Supporting axiom-clean infrastructure: `reach_ind` (edge-closure induction principle for
  the concrete BFS), `reach_edgeClosed` + `reach_sat` (fixed-fuel closure saturates under
  `InRange` — the bounded monotone-chain argument, fully constructive with decidable steps
  and explicit witnesses), `relabelV_inj_or` (merge map injective off the collapsed pair
  `{a,b}`).

### Proof method (genuine, non-vacuous)

The transport is proved by the **least-fixpoint / closure induction principle** for the
concrete `reachClosure`, not by fuel counting. Both directions are edge-closure inductions;
they use that under `InRange` the fixed-fuel closure is a fixpoint (`reach_sat` → edge-closed
via `reach_edgeClosed`), plus `relabelV_inj_or` (two labels sharing a merge image are equal
or the pair `{a,b}`, which the head edge re-identifies inside `G`). Non-vacuous: hypotheses
are satisfiable (e.g. `n=2,a=0,b=1,A=[]`) and the biconditional is genuinely false for wrong
inputs (the refutations).

## Is (P)/(T′) closed?

**(P) BFS core: yes** — the one weightless BFS fact left on Sub-wall A's (P) is proved
(guarded) and axiom-clean. The non-loop `treeCount` half of the deletion–contraction
recursor is closed in-range.

**(T′) tree-graph atom: NOT discharged.** The prompt's plan (oriented recursor → `penroseIneq`
→ `penroseDom` → `(T′)`) is blocked by the correction plus pre-existing separate legs. The
remaining, now-sharp residuals:

1. **Const-`Csum` non-loop half, guarded.** Analogue of `treeCountContract_inRange` for
   `Csum (wConst c)` (symmetric; consumes the same `spansContractLt_inRange`). Mechanical,
   not yet written. (The existing `Csum_nonloop_const_reduced` takes the *unguarded*
   `SpansContractLt` — now known FALSE — so it is inapplicable and must be re-derived
   in-range.)
2. **Head re-orientation.** `penroseIneq_fuel` recurses on arbitrary head edges `(a,b)`, so
   it hits `a>b` (and `a=b`). The guarded contraction needs `a<b`. Requires head-swap
   invariance of `spans`/`treeCount`/`Csum` (`(a,b)`↔`(b,a)`, undirected) to reorient
   `a>b`; the loop `a=b` branch is already closed unconditionally (`dcLoopBranch_closed`).
3. **`InRange` threading** through `penroseIneq_fuel` / a guarded `DCHyp` (contraction
   preserves `InRange`: `relabelV_lt` maps `<n` to `<n-1`; deletion keeps `rest` in-range —
   both facts are available here).
4. For the full `(T′)` beyond leg (P): the **Ursell pin** (`UrsellPin`), **leg (C) Cayley**
   (`cayleyMax`), and **leg (A)** `CubicEulerBound` — all named-open elsewhere.

Separately, **A2/Racah** remains the other open Sub-wall-A atom (blocked on a ring
normaliser), as noted in the prompt.

So: Sub-wall A's (P) BFS residual is done (guarded) and the record corrected; (T′) is
materially advanced (loop branch + non-loop `treeCount` half closed in-range) but not closed.

## Files touched

* NEW `lean/YMGap/Continuum/SpansContractInRange.lean` (the whole deliverable).
* `lean/YMGap.lean` — added the import.
* `lean/YMGap/Continuum/SpansContractProof.lean` — corrected the false "NOT refutable"
  docstring claim on `ReachTransport` (prose only).

## Verification

* `lake build` exit 0 (786 jobs); `lake build YMGapGuard` → "frontier-guard OK: 5 …".
* `#print axioms` on `reachTransport_inRange`, `spansContractLt_inRange`,
  `treeCountContract_inRange`, `reach_sat`, `reach_edgeClosed`, `relabelV_inj_or`, and both
  refutations → all `[propext, Quot.sound]`.
* Non-vacuity: refutations are genuine `decide`-checked counterexamples; the guarded theorem
  is a real biconditional with satisfiable hypotheses. `C` (the const/`Csum` object) unchanged.
