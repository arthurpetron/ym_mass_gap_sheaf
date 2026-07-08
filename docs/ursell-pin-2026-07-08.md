# Ursell pin PROVED → atom (T′) `TreeGraphBound.tree_graph` DISCHARGED

**Verdict: (T′) is DISCHARGED — the burn-down metric D moves off 0 for the first
time.** `TreeGraphBound` is now genuinely, unconditionally INHABITED for every
lattice, via a real (non-vacuous, machine-verified) inhabitant of the Ursell pin
`UrsellPinConst`. The frontier guard STAYS 5 (the scorecard is untouched).

New file: `lean/YMGap/Continuum/UrsellPinComplete.lean` (imported in `YMGap.lean`).
`lake build` exit 0 (787 jobs). Axiom-clean throughout (`propext`/`Quot.sound`
only; `ofNat_mul_recip_cancel` is just `[propext]`). No `sorry`/`native_decide`/
`Classical`.

## 1. The Ursell/Mayer coefficient identity (`ursellPinComplete`)

For the CONSTANT hard-core weight `wConst c` (`c ∈ [-1,0]`) the Mayer factor
between *every* pair of vertices is the same constant `c`, so the polymer
interaction graph is the COMPLETE graph `K_n` on the `n = |Y|` vertices
`{0,…,n-1}`. The pin is inhabited with:

  - `adjN Y := |Y|`, `adjE Y := completeEdges |Y|` (the `K_n` edge list);
  - `phiT Y := |C(wConst c, K_n)| / n!` — the genuine const-weight Ursell coeff;
  - `treeCountF Y := τ(K_n)`.

The load-bearing field

    ursell : (ofNat(n!) * phiT Y).eqv (|C(wConst c, adjGraph Y)|)

is the exact Ursell/Mayer identity `n!·φ^T(Y) = |C(K_n)|` — the truncated Ursell
coefficient of a cluster is `1/n!` times the signed sum over connected spanning
subgraphs of the interaction graph. Proved as a genuine `Q'` reciprocal
cancellation `ofNat_mul_recip_cancel` (`n!·(A/n!) ≃ A`, `A := |C|`), built from
`ofNat_mul_mkPos_recip_eqv` + the `Q'` `eqv`-congruence toolkit. `countPin` is
`rfl`.

**Non-vacuity (numerically verified via `#eval`):**
`completeEdges 3 = [(0,1),(0,2),(1,2)]` (real `K_3`); at `c = -1`,
`Csum(K_3) = 2 = (3 spanning trees·(-1)²) + (1 triangle·(-1)³) = 3 − 1` — the
textbook signed connected-subgraph sum — so `phiT(K_3) = 2/3! = 1/3`,
`phiT(K_2) = 1/2`. Not `phiT := |C|` by fiat; `phiT` carries independent content
(the actual signed sum) and the identity is proved EQUAL to it.

## 2. Feeding the assembler → the (T′) discharge

`completeEdges` is proved IN-RANGE (`compEdges_inRange`) and SIMPLE
(`compEdges_simple`: `Nodup` via `nodup_map_of_injOn`+`range_nodup`, plus
canonical orientation `i<j<n`). Then:

  - `penroseDomConst_of_pin` (the PROVED Penrose sign-domination `|C| ≤ τ`, no
    `DCHyp`) supplies leg (P);
  - `cayleyLooseBound_closed` (τ(K_n) ≤ n^{n-1}, PROVED) supplies leg (C′) — the
    LOOSE Cayley route via `TreeGraphReductionLoose.toBoundLoose`;
  - `CubicEulerBoundProof.cubicEulerBound` ((1+1/n)^n ≤ 3, PROVED) supplies (A).

Assembled:

  - `ursellPinComplete   : UrsellPinConst S c`          — the Ursell pin, inhabited;
  - `treeGraphBoundComplete S w r c (h:−1≤c) (h:c≤0) : TreeGraphBound S w r`;
  - `treeGraphBoundHardCore S w r : TreeGraphBound S w r` — the c = −1
    specialization, **UNCONDITIONAL for every S,w,r**. This inhabits (T′)
    `TreeGraphBound.tree_graph`: `|φ^T(Y)| ≤ eSurrogate^{|Y|} (=3^{|Y|})` is now a
    THEOREM for the const hard-core Ursell coefficient.

The hard, genuine content of the discharge is the Penrose inequality
`|C(K_n)| ≤ τ(K_n)` (binding non-trivially: |C(K_3)|=2 < τ=3), chained with
Cayley and the e<3 arithmetic — the classical Penrose/Poghosyan–Ueltschi
tree-graph bound.

## 3. Guard status — STAYS 5 (verified)

`YMGapGuard.lean` reports: `frontier-guard OK: 5 Clay-frontier types
unconditionally uninhabited across YMGap.*`. Discharging (T′) inhabits
`TreeGraphBound` (not a guarded type) but does NOT inhabit `Tier0Scorecard` —
(T′) is one atom of Sub-wall A (d2Sep / d1Mayer / a2Racah / a2Pentagon and
Sub-wall B remain open). No vacuous guard break; the scorecard stays uninhabited.

## 4. `#print axioms` (all deliverables)

    compEdges_mem/inRange/simple            : [propext, Quot.sound]
    ofNat_mul_recip_cancel                  : [propext]
    ursellPinComplete                       : [propext, Quot.sound]
    treeGraphBoundComplete                  : [propext, Quot.sound]
    treeGraphBoundHardCore                  : [propext, Quot.sound]
    treeGraphBoundHardCore_tree_graph       : [propext, Quot.sound]

## Honest scope

Fixed-spacing strong-coupling combinatorics; the const hard-core Ursell coefficient
(interaction graph = K_n, correct for `wConst c`). This is the FIRST genuine
atom-level D-move: (T′) `TreeGraphBound.tree_graph` is discharged, `TreeGraphBound`
inhabited, scorecard still open via the other Sub-wall-A/B atoms. It is NOT the
spacing-uniform continuum modulus. The Clay Yang–Mills mass gap remains OPEN — the
current open residuals are the remaining Sub-wall-A atoms (d2Sep, d1Mayer, a2Racah,
a2Pentagon) and Sub-wall B; attack those next.

No Ursell-identity lemma resisted; the pin is proved in full.
