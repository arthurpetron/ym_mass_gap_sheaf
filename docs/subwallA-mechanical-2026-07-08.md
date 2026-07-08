# Sub-wall A leg (P) — mechanical finish + (T′) status

**Deliverable file:** `lean/YMGap/Continuum/PenroseConstInRange.lean` (new, ~470 lines, untracked/uncommitted)
**Import wired:** `lean/YMGap.lean:653` (`import YMGap.Continuum.PenroseConstInRange`)

## Verdict (one line)

The three requested mechanical pieces are **genuinely proved, axiom-clean, non-vacuous**, and the leg-(P) Penrose inequality `|C(G)| ≤ τ(G)` is now a **THEOREM** for the constant hard-core weight in-range (the refuted `DCHyp` residual is DISCHARGED, not merely reduced). **(T′) does NOT fully discharge**: it is reduced to three named residuals — the **Ursell pin**, **Cayley leg (C)**, **CubicEulerBound leg (A)** — with leg (P) removed from the residual set.

## Build / guard / axioms

- `lake build` → **exit 0**, 0 errors, whole library green.
- Frontier guard → **`frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`**. The guard did NOT react: (T′) `TreeGraphBound.tree_graph` is not a frontier type, and `treeGraphBound_of_const` is a *conditional* producer (3 open hypotheses), so no unconditional inhabitant of any frontier type was created. Guard stays 5 — correct, because (T′) is reduced, not closed.
- `#print axioms` on every load-bearing decl → `[propext, Quot.sound]` only (`gsum_guard_congr` = no axioms). No `sorry`, no `native_decide`, no `Classical.*`, no new `axiom`. Mathlib-free (`Q'`/`Nat`/`List`/`Bool`).
- Non-vacuity spot-check (throwaway probe, since deleted): on the triangle `[(0,1),(1,2),(0,2)]`, `treeCount 3 = 3`, `spans 3 = true`, `spans 3 [(0,1)] = false`, and `treeCount 3 [(1,0),…] = treeCount 3 [(0,1),…]` (head-swap) all evaluate by `decide`. The objects have real content.

## The three mechanical pieces (all PROVED)

### (1) const-Csum non-loop guarded half — `Csum_nonloop_const_inRange`
For `a<b<n`, `InRange n rest`:
`C(n,(a,b)::rest) ≃ C(n,rest) + c·C(n-1, contractEdges a b rest)`.
Symmetric to the already-closed weightless `treeCountContract_inRange`. New tool `gsum_guard_congr` (gsum congruence under *pointwise guard agreement on the actual power-set members*) lets the PROVED in-range `spansContractLt_inRange` (applied per member via `inRange_of_mem_sublists`) replace the FALSE global funext the old `Csum_nonloop_const_reduced` used against the unsatisfiable unguarded `SpansContractLt`. Value side uses `edgeProd_const_map` (relabel-invariance of the constant weight).

### (2) a>b head re-orientation — `relaxEdge_swap` → `spans_head_swap` → `Csum_headswap_const` / `treeCount_head_swap`
Genuine undirected head-swap invariance, proved from the ground up: `relaxEdge (a,b) R = relaxEdge (b,a) R` (4-way case split on membership), lifted through `relax`/`reachClosure` to `spans n ((a,b)::A) = spans n ((b,a)::A)`, then to `Csum (wConst c)` (value `c` symmetric) and `treeCount` (delete-split + length-blind guard). This closes the `a>b` branch of the recursor by reducing it to the oriented `b<a` non-loop identity. Combined with `a<b` (done) and `a=b` (loop, done) → **all edge orientations covered**.

### (3) InRange-threaded Penrose inequality — `penroseIneqConst_fuel` / `penroseIneqConst`
`|C(G)| ≤ τ(G)` for `wConst c` (`-1≤c≤0`) on any in-range graph, by fuel induction with **NO `DCHyp`**. `InRange` is preserved under deletion (sublist) and contraction (`relabelV_lt`), so the guarded lemmas apply at each step. Three head cases discharged: loop (`dc_loop_Csum` + `treeCount_loop_closed`, factor `1+c∈[0,1]`), oriented non-loop (piece 1 + `treeCountContract_inRange`, factor `c∈[-1,0]`), re-oriented non-loop (piece 2 head-swap + oriented identity). Shared analytic assembly factored into `nonloop_assemble` (triangle bound + `abs_mul_le_of_factor`). This is the const-weight, in-range replacement for the parent `penroseIneq` that rested on the refuted `DCHyp`.

## (T′) discharge attempt — honest geography

- `penroseDomConst_of_pin` — leg (P) `penroseDom` (`n!·phiT Y ≤ ofNat(treeCountF Y)`), PROVED for the const weight modulo **only** the Ursell pin `UrsellPinConst` (Ursell coefficient identity + in-range polymer connectivity graph). No `DCHyp`.
- `treeGraphReductionOfConst` — builds a `TreeGraphReduction` whose `penroseDom` field IS `penroseDomConst_of_pin` (leg (P) discharged) and whose `cayleyMax` field is the Cayley input.
- `treeGraphBound_of_const` — from `UrsellPinConst` + Cayley (`hCayley`) + `CubicEulerBound` (`hEuler`), CONSTRUCTS a `TreeGraphBound`, i.e. discharges the atom (T′) `TreeGraphBound.tree_graph` via `TreeGraphReduction.toBound`.

So **(T′) is reduced from `{DCHyp/Penrose-inequality (P), Cayley (C), CubicEulerBound (A), Ursell pin}` to `{Cayley (C), CubicEulerBound (A), Ursell pin}`** — leg (P)'s Penrose inequality (the sole genuinely-new mathematics of the reduction) is now a proved theorem.

## Sub-wall A residuals that remain (named sharply)

1. **Ursell pin** — `UrsellPinConst` uninhabited: the Ursell↔connected-graph coefficient identity `n!·|φ^T(Y)| = |C(adjGraph Y)|` for the const weight, over an in-range polymer connectivity graph. This is the sole leg-(P) residual now (the Penrose inequality half is proved).
2. **Cayley leg (C)** — `treeCount Y ≤ n^{n-2}` (`hCayley`); moderate combinatorics, maximiser `K_n`. Lives in the `Cayley*` files (~80% done there), not yet assembled to this signature.
3. **CubicEulerBound leg (A)** — `(1+1/n)^n ≤ 3`; elementary `e<3` bound, everything downstream already proved in `TreeGraphBoundProgress`.
4. **A2 / Racah** — upstream Sub-wall-A input, separate front (RACAH-SAALSCHUTZ agent's `RacahSaalschutz.lean` — untouched by me), still open.

## Coordination / hygiene

- Owned/edited only Penrose/Cayley/tree territory: created `PenroseConstInRange.lean`, added one import to `YMGap.lean`. **Did NOT touch** `RingNormaliserStream.lean`, `RacahSaalschutz.lean`, `RacahDougallWZ`, `BiedenharnElliott`.
- Main tree (no worktree). Committed nothing. C unchanged.
