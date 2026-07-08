# Sub-wall A — honest close/verdict on (P) and (D1)

Build: `lake build YMGap YMGapGuard` → **exit 0** (784 jobs). Guard:
`frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`.
All new declarations axiom-clean (`propext`/`Quot.sound` only). No `sorry`,
no `native_decide`, no new axioms. C unchanged.

## Bottom line

**Neither (P) nor (D1) can be honestly *closed* as the task posed them — and this
is not for lack of effort: both are already machine-characterized in-tree as walls
whose naive forms are FALSE / UNSATISFIABLE. Faking either is exactly what the
honesty contract forbids.** What is genuinely closeable on the (P) path I closed;
what remains is named sharply. Details:

---

## (D1) `MayerUrsellIdentity_z4` — PROVABLY UNSATISFIABLE (cannot be closed)

`MayerUrsellZ4.mu_z4_total_weight_le_zero` (green, axiom-clean) PROVES that **every**
inhabitant `MU : MayerUrsellIdentity_z4 p` forces the total spectral weight of its
correlator to be `≤ 0`:

    corr MU.model 0 ≤ clusterSpanSum … 0 = 0   (empty sum at d=0)
    corr MU.model 0 ≃ Σ_i (MU.model).w_i       (corr_zero)
    ⟹  Σ_i w_i ≤ 0  ⟹  the trivial ZERO model.

So the ONLY inhabitant is the zero model — which is precisely the `offCorr:=0`
Rule-6 fake the task forbids. **Leaving `MayerUrsellIdentity_z4` uninhabited is the
CORRECT state**, not a gap. The task's instruction to "supply the genuine z4 witness
→ discharge" is mathematically impossible without faking.

The honest, satisfiable replacement is already wired in-tree (not by me): the
free-`tailLen` `Ursell4DProgress.BridgeDecomposition` (RHS at `d=0` includes the
size-`k` bridge term, escaping the `d=0` zero-forcing), collapsed by
`MayerUrsellZ4.splitOfAtoms` onto exactly the two named atoms **(T′)**
`TreeGraphBound.tree_graph` and **(D1-proper/D2)** `BridgeDecomposition.decompose` /
`SepLatticeZ4`. Count, threshold (`ρ4 = 15/32 < 1`), tree-graph assembly and the
geometric decay `≤ 2·(15/32)^d` are all PROVED. Non-vacuity is certified by the
genuine tree instance `nonvacuity_tree` (backed by `treeWilsonG_decay`, not the
zero model). **(D1) remains the multi-plaquette/loopy wall; uninhabited is correct.**

---

## (P) Penrose deletion–contraction — loop branch CLOSED; non-loop reduced to ONE BFS residual

Two pre-existing in-tree facts frame the honest state of `DCHyp`/`penroseIneq`:

* the **non-loop `Csum` half is machine-REFUTED for general `w`**
  (`PenroseDCContract.dc_nonloop_Csum_refuted`): `contractEdges` relabels vertices,
  `edgeProd` re-reads `w` at the NEW labels, so the identity is false off the
  relabel-invariant weights. Hence `DCHyp w` / `penroseIneq`'s hypothesis is **not
  inhabitable for a general repulsive `w`** — the task's "inhabit `penroseIneq`" is
  impossible as stated.
* the connectivity/`treeCount` contract half needs the ORIENTATION guard `a < b`
  (not `a ≠ b`): `SpansContractProof.spansContract_refuted`.

Also already done in-tree: **`SpansMinEdgesProof.spansMinEdges` is fully PROVED**
("spanning ⟹ `n ≤ |A|+1`", via a monovariant potential over the BFS).

### NEW — `YMGap/Continuum/PenroseConstWeightDC.lean` (all green, axiom-clean)

1. **`treeCount_loop_closed` (a genuine CLOSE, no residual):**
   `treeCount n ((a,a)::rest) = treeCount n rest`, PROVED from `spansMinEdges`
   + `spans_self_loop` + `treeCount_cons_split`. A head self-loop would need
   `|s| = n-2` edges to span with `|(a,a)::s| = n-1`, which `spansMinEdges`
   forbids, so the head-containing branch is empty.

2. **`dcLoopBranch_closed` (the WHOLE loop branch of the recursor, general `w`):**
   `Csum` half = `dc_loop_Csum` (pre-existing, general), `treeCount` half =
   `treeCount_loop_closed`. **The loop branch of `DCHyp` is now a theorem — no
   residual, no orientation guard, no weight restriction.**

3. **`Csum_nonloop_const_reduced` (CORRECTION + reduction to ONE residual):**
   the non-loop `Csum` identity is FALSE for general `w`, but for the
   physically-correct constant/hard-core weight `wConst c ≡ c` (`c ∈ [-1,0]`) it is
   TRUE, because `edgeProd (wConst c)` is relabel-invariant (`edgeProd_const_map`).
   For `a < b < n`:

       C(n,(a,b)::rest) ≃ C(n,rest) + c·C(n-1, contractEdges a b rest)

   PROVED from the SINGLE correctly-guarded residual
   `TreeCountContractProof.SpansContractLt` — the *same* residual the weightless
   `treeCount` non-loop half (`treeCountContractGuarded`) already reduces to.
   Supporting: `edgeProd_const_map`, `gsum_map` (both axiom-free).

### Net effect on (P)

For the constant hard-core weight, **every** half of the deletion–contraction
recursor is now either closed outright (both loop halves; the delete split) or
reduced to the ONE weightless BFS fact `SpansContractLt`
(⟸ `SpansContractProof.ReachTransport`):

| branch | half | status |
|---|---|---|
| loop | `Csum` | CLOSED (`dc_loop_Csum`, general `w`) |
| loop | `treeCount` | **CLOSED (new `treeCount_loop_closed`)** |
| non-loop | `treeCount` | reduced to `SpansContractLt` (`treeCountContractGuarded`) |
| non-loop | `Csum` (const `w`) | **reduced to `SpansContractLt` (new `Csum_nonloop_const_reduced`)** |
| delete split | both | CLOSED (`Csum_delete_split`, general `w`) |

The general-`w` refutation is thereby localized precisely to the non-constant
weights; the physically-relevant hard-core case rests on the single open BFS
residual.

### The remaining (P) residual, named sharply

**`SpansContractProof.ReachTransport`** — the exact-fuel BFS reachability
correspondence under the vertex-merge `relabelV a b` (`a < b < n`). It implies
`SpansContractLt` (via `spansContractOriented_of_transport`), which closes both
non-loop halves above. It is genuinely TRUE (brute-force validated on small
graphs) but UNBUILT: proving it rigorously requires BFS walk-transport + fuel
saturation + the exact `n`/`n-1` fuel alignment, with essentially no reusable
in-tree infrastructure (no reachability monotonicity/walk lemmas exist yet). It
was NOT closed this session; left uninhabited, not faked.

Note also: even with `ReachTransport`, inhabiting `penroseIneq`/`DCHyp` **as
written** still fails, because they quantify over general `w` and arbitrary head
orientation. A full hard-core `penroseIneqConst` needs, additionally, an
*oriented* fuel recursor (edges normalized to `a < b`, orientation-preserved
under contraction) — a further reformulation, not the stated object.

---

## Did any Sub-wall-A atom react?

No — correctly. Sub-wall A's atoms (`FrontierDAG`: `tTree`=T′, `d1Mayer`=D1,
`d2Sep`=D2, `a2Racah`, `a2Pentagon`, `coreB`) are all still uninhabited, so the
guard stays at 5. My work advanced the (P) machinery *feeding* `tTree` (via
`penroseDom`/`TreeGraphReduction`) but did not discharge `tTree` (which still needs
the full oriented hard-core `penroseIneq` + leg-C Cayley + leg-A `CubicEulerBound`),
and (D1) is provably unsatisfiable. **Sub-wall A is NOT done.**

## Verdict

- (P): loop branch **closed**; non-loop (const weight) **reduced to the single BFS
  residual `ReachTransport`**; general-`w` `DCHyp`/`penroseIneq` unclosable as
  stated (refuted). NOT fully closed.
- (D1): **provably unsatisfiable** — cannot be closed; uninhabited is correct.
- Sub-wall A: **NOT done.** Sole remaining genuine-TRUE (P) residual =
  `ReachTransport`; (D1)/(T′)/(D2) remain the loopy-geometry walls.

#print axioms (all `[propext, Quot.sound]` or none):
`treeCount_loop_closed`, `dcLoopBranch_closed`, `Csum_nonloop_const_reduced`,
`edgeProd_const_map` (none), `gsum_map` (none), `penroseIneq`,
`mu_z4_total_weight_le_zero`.
