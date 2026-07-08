# (D1) `correlator_le_span_sep` — rigorous satisfiability audit + genuine reduction

**File:** `lean/YMGap/Continuum/MayerUrsellZ4Physical.lean` (new; registered in `lean/YMGap.lean`)
**Build:** `lake build` exit 0 (789 jobs). **Guard:** `frontier-guard OK: 5 Clay-frontier types` (STILL 5). **Axioms:** every decl ⊆ {propext, Quot.sound}.

## Honest verdict up front

**(D1) `correlator_le_span_sep` is NOT discharged.** It is genuinely REDUCED. The target
`MayerUrsellIdentity_z4_v2.correlator_le_span_sep` cannot be honestly inhabited in one pass
because — exactly as the prior agent warned — the structure's `model : SpectralModel` field is
**FREE/unpinned** (the phantom-parameter trap, one level up from `Ursell4DBridgePin.castBridge`).
I did NOT fake it and did NOT fall into the trap; I machine-proved the trap and then delivered the
genuine forward reduction, isolating the exact resisting piece.

## What was PROVED (axiom-clean, non-vacuous)

### §1 Phantom/vacuity diagnostic — inhabiting the BARE v2 is a Rule-6 fake
- `diagModel_corr_offdiag_zero : ∀ d ≥ 1, (corr diagModel d).eqv 0` — the trivial single-mode
  model (eigenvalue `λ₀ = 0`) has an identically-zero connected correlator off the diagonal
  (`corr d = ½·0^d ≃ 0`).
- `clusterSpanSum_nonneg` (via `finSum_nonneg'` + `kpTerm_z4_nonneg`) — the RHS is `≥ 0`.
- `diagModel_satisfies_sep` + (pre-existing) `diagModel_satisfies_diag` ⟹ `diagModel_vacuousWitness :
  MayerUrsellIdentity_z4_v2 p` — a full inhabitant of the BARE structure whose correlator carries
  **no z4 physics**. This is the machine-checked proof that inhabiting the bare v2 is vacuous — the
  same reason the prior agent left it uninhabited. It is deliberately NEVER wired into
  `BridgeDecomposition`/`SubWallA`/`Tier0Scorecard`.

### §2 Genuine forward reduction — pin the model, discharge the KP assembly
- `PhysicalMayerUrsellZ4 p` — the honest, non-phantom residual. It PINS the model by putting
  `corr model` on the LHS of the multi-plaquette Mayer–Ursell expansion, and carries `phiT`, `zeta`,
  `zeta_nonneg`, `tree_graph` (T′), `activity_le`, the `expansion_sep` identity, and `diag_normalization`.
- `physical_to_v2 : PhysicalMayerUrsellZ4 p → MayerUrsellIdentity_z4_v2 p` — **the load-bearing
  reduction.** `correlator_le_span_sep` is proved from `expansion_sep` by discharging the KP-assembly
  half termwise: each `animalCount(d+m)·(phiT(d+m)·zeta(d+m)) ≤ kpTerm …(d+m)` via the PROVED
  `Ursell4DProgress.kpTerm_from_atoms` (count folded, `phiT·zeta·eSurrogate` collapsed into `kpTerm`),
  lifted by `CharacterTail.finSum_le_termwise` into the definitional `clusterSpanSum`.
- `physical_to_bridge` — composes with the prior agent's `bridgeDecomposition_of_physical`, wiring the
  physical Mayer–Ursell expansion all the way to the frontier (D1) node `BridgeDecomposition`
  (CONDITIONAL on the open residual, so the guard is untouched).

Net effect: `correlator_le_span_sep` ⟺ (multi-plaquette expansion identity `expansion_sep`) ∧ (T′)
∧ (activity, already backed in-repo). The KP-assembly half is now DISCHARGED.

## The EXACT resisting piece (the wall)

`PhysicalMayerUrsellZ4.expansion_sep` — the genuine z4 **multi-plaquette** Mayer–Ursell expansion
identity `∀ d ≥ 1, corr model d ≤ Σ_{m<d} animalCount(d+m)·(phiT(d+m)·zeta(d+m))`. This IS the
`MayerClustering.MayerUrsellIdentity` residual: **DISCHARGED for the single-line chain**
(`mayerUrsell_singleLine` via the real `wilsonG_decay`), **OPEN for the multi-plaquette/loopy
correlator**, and its size-floor geometry is the still-missing (D2) `Ursell4DProgress.SepLatticeZ4`.
This is not a combinatorial gap I can close by reusing the KP/Penrose machinery — that machinery
(the pin) discharges the neighbouring (T′) tree-graph majorant on the (T) side, whereas `expansion_sep`
is the physical (D) side, as the prior agent's `Ursell4DBridgePin` correctly established.

## Why this is Category-A math but still resists here

The Mayer–Ursell / KP bound (Brydges, Kotecký–Preiss) is standard **once the physical correlator is
represented as a convergent polymer expansion over the z4 lattice**. The repo has the KP *convergence*
layer (geometric tail, `clusterSpanSum_decay`, `spanning_cluster_term_le` consuming
`connected_spanning_size_ge`) and the *single-line* expansion identity, but **not** a constructive
multi-plaquette expansion identity linking the actual z4 connected correlator (as a `SpectralModel`)
to its connected-cluster sum. That identity — over the z4 plaquette graph, needing (D2)'s BFS metric —
is the genuine open content. Producing it would require constructing the physical z4 correlator's
polymer expansion, which is not present.

## Guard-semantics check (as mandated)

`YMGapGuard` flags UNCONDITIONAL inhabitants of its 5 fixed frontier types
(`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`).
`MayerUrsellIdentity_z4_v2` is NOT among them. `diagModel_vacuousWitness` is unconditional but of a
non-guard type and reaches no guard type (SubWallA still needs open `tTree`/`a2Pentagon`; Tier0Scorecard
needs `subB`). `physical_to_v2`/`physical_to_bridge` are CONDITIONAL (open `PhysicalMayerUrsellZ4`
hypothesis) — not flagged. Verified: guard stays **5**; `frontier-guard OK`. progress_metric: D=0, guard=5.

## `#print axioms` (all load-bearing decls)
```
finSum_nonneg'              : [propext]
kpTerm_z4_nonneg            : [propext, Quot.sound]
clusterSpanSum_nonneg       : [propext, Quot.sound]
diagModel_corr_offdiag_zero : [propext]
diagModel_satisfies_sep     : [propext, Quot.sound]
diagModel_vacuousWitness    : [propext, Quot.sound]
physical_to_v2              : [propext, Quot.sound]
physical_to_bridge          : [propext, Quot.sound]
```

## Bottom line
(D1) is the **second Category-A atom REDUCED, not closed**. The KP-assembly half and the phantom
diagnostic are proved axiom-clean; `correlator_le_span_sep` for the physical z4 model is pinned to
the single named residual `expansion_sep` (the multi-plaquette Mayer–Ursell expansion identity) + (T′).
Guard intact at 5. Clay YM mass gap OPEN.
