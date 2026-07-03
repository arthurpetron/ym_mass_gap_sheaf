# `d2Sep` / `SepLatticeZ4` metric-sufficiency

**Question.** The Sub-wall-A geometry residual `(D2)` is a `SepLatticeZ4`
metric refining the closed 4D count lattice `z4Chain`. Two candidate
constructions inhabit it:

- **(i)** the L¹ coordinate-sum witness `z4Sep` (already built,
  `SepLatticeZ4Close.lean:105`), whose `dist` collapses to `0` along
  constant-sum directions; and
- **(ii)** a directional L∞ / BFS metric `maxᵢ|vᵢ(p)−vᵢ(q)|`, which never
  collapses but whose triangle inequality is a 4-way `max`/`omega` split.

Is (i) sufficient for everything currently wired, or is (ii) mandatory?

**Verdict: (i) — the L¹ coordinate-sum witness SUFFICES** for every consumer
wired today. A directional L∞ metric is *not required* by anything on a wired
path. Directionality is a **latent** requirement, gated on one specific
(currently uncalled) supply point.

---

## 1. What `SepLattice` actually exposes

`SepLattice` (`PinnedCluster.lean:234`) extends `Lattice` with exactly one
metric field and three axioms — nothing else:

- `dist : Plaquette → Plaquette → Nat`
- `dist_self  : ∀ p, dist p p = 0`                    (`:238`)
- `dist_adj_le : ∀ p q, Adjacent p q → dist p q ≤ 1`   (`:241`)
- `dist_triangle : ∀ p q r, dist p r ≤ dist p q + dist q r` (`:243`)

`SepLatticeZ4 := { S : SepLattice // S.toLattice = z4Chain.toLattice }`
(`Ursell4DProgress.lean:329`).

The decisive structural observation: **no consumer ever reads a raw `dist`
value**. In every place `dist p q` appears, it appears only as the RHS of a
`≤` that is discharged by the three axioms above (never by evaluating the
metric). So a consumer is sensitive to the *choice* of metric only through
which of `{dist_self, dist_adj_le, dist_triangle}` it invokes — and any lawful
`SepLattice` discharges all three by definition.

---

## 2. Per-consumer property table

Enumerating every consumer of `d2Sep.val` / the metric:

| Consumer | Location | `SepLattice` property invoked | Reads raw `dist`? |
|---|---|---|---|
| `SubWallA.tTree : TreeGraphBound d2Sep.val w4 gr` | `Tier0Scorecard.lean:133` | **none** — `TreeGraphBound` (`Ursell4DProgress.lean:244`) touches only `S.toLattice` to form `Polymer S.toLattice`; `phiT`/`phiT_nonneg`/`tree_graph` never mention `dist` | No |
| `subA_tree_graph` (projection of `tTree`) | `Tier0Scorecard.lean:180` | **none** — stated over `Polymer F.subA.d2Sep.val.toLattice`, delegates to `tTree.tree_graph` | No |
| `connected_spanning_size_ge` (the sole genuine metric engine) | `PinnedCluster.lean:347` | routes ONLY through `dist_le_pathLen` | via axioms below |
| ↳ `dist_le_pathLen` | `PinnedCluster.lean:314` | `dist_self` (`:320`), `dist_adj_le` (`:324`), `dist_triangle` (`:325`) — and nothing else | axioms only, raw `dist` never evaluated |
| `spanning_cluster_term_le` (wraps the engine) | `MayerClustering.lean:180` | none beyond the engine; takes `hsep : d ≤ S.dist p q` as an **input hypothesis** — and is **DEFINED-BUT-UNUSED** (no proof-term caller anywhere) | supplies, does not prove |
| `clusterSpanSum_decay` (the wired decay) | `MayerClustering.lean:216` | **none** — proof is `unfold clusterSpanSum; exact pinnedClusterTail cc hw r hthr d d` (`:220–221`); **bypasses** the metric engine entirely | No |

**Union of properties actually invoked across all consumers:**
`{dist_self, dist_adj_le, dist_triangle}` — never the raw `dist` values.

---

## 3. Why the L¹ witness discharges all three axioms

`z4Sep` (`SepLatticeZ4Close.lean:105`) genuinely inhabits `SepLattice` over the
closed degree-24 Z⁴ plaquette lattice with `dist := z4dist`, the L¹
coordinate-sum potential difference (`z4dist p q := (sPlaq p − sPlaq q) + (sPlaq q − sPlaq p)`,
`:96`):

- `dist_self`  — `simp [z4dist]; omega` (`:108`).
- `dist_adj_le ≤ 1` — the load-bearing case (`:109–118`). A shared boundary
  edge places its base in the width-1 window `[sPlaq p, sPlaq p+1]` of **both**
  plaquettes (`edge_base_sum`, `:83`, proved from `sVertex_addE`), so the two
  potentials differ by at most `1`. This is the one axiom that genuinely
  constrains the construction.
- `dist_triangle` — `simp [z4dist]; omega` (`:119`).

`SepLatticeZ4_witness := ⟨z4Sep, rfl⟩` (`:126`) inhabits the subtype (`rfl`
because both `.toLattice`s are definitionally `z4Lattice`). The potential is
genuinely unbounded (`sPlaq_addE`, `:131`), so this is **not** a faked
zero-distance metric like `PinnedCluster.toySep` (`:250`, `dist ≡ 0`).

Since every consumer that invokes a metric property invokes only these three
axioms — or invokes no metric property at all — the L¹ `z4dist` is sufficient
for every currently-wired consumer.

---

## 4. Honest caveat: why L∞ is *latent*, not current

The L¹ collapse (`z4dist = 0` along constant-sum directions, e.g. displacement
`+e_x, −e_y`) is invisible to the three axioms — it discharges `dist_adj_le`,
`dist_self`, `dist_triangle` regardless — but it *would* bite at one specific
point: where a caller must **supply** `hsep : d ≤ S.dist p q` for a physical
operator pair at genuine bridging distance `d`. If `S.dist p q = 0` for a pair
the physics separates by `d > 0`, that supply is unprovable.

That supply point is **exactly** `spanning_cluster_term_le`
(`MayerClustering.lean:186`, the `{d : Nat} (hsep : d ≤ S.dist p q)` argument).
And `spanning_cluster_term_le` is **never called**: a search over the Lean
sources finds it only in docstrings and the axiom audit — it has zero
proof-term callers. The wired decay `clusterSpanSum_decay` (`:216`) derives the
geometric tail directly from `PinnedCluster.pinnedClusterTail` and bypasses the
geometric engine entirely. So **no wired path demands `d ≤ S.dist p q` from
geometry**; every wired path either uses only `.toLattice` (`tTree`) or gets its
decay combinatorially (`clusterSpanSum_decay`).

The strictly-stronger drop-in becomes mandatory **only if** the Ursell decay is
re-routed through `spanning_cluster_term_le`, i.e. only if some future caller
must produce `hsep` from the metric for a physical pair. That drop-in is the
per-coordinate L∞ metric `maxᵢ|vᵢ(p)−vᵢ(q)|`, whose `dist_adj_le` still holds
(one coordinate changes by ≤1 per adjacency step) and whose collapse-freeness is
exactly what would let a physical pair supply `hsep`; its triangle inequality is
a 4-way `max`/`omega` case split rather than the single scalar `omega`. This is
precisely the contingency flagged in the `SepLatticeZ4Close.lean` honest-scope
note (`:33–44`).

---

## 5. Do 11.2 / 11.3 need directional separation?

**No.** The two remaining `d2Sep`-coupled Sub-wall-A atoms both invoke zero
metric properties, so both close over the L¹ witness:

- **(T′) `tTree` / `TreeGraphBound.tree_graph`** — uses only
  `d2Sep.val.toLattice` (to form `Polymer …`); the "(T′)/(D2) coupling"
  (`Tier0Scorecard.lean:57,122`) is purely **nominal**: `TreeGraphBound`'s first
  argument is a `SepLattice`, but only its `.toLattice` projection is
  load-bearing, and that projection is pinned to `z4Chain.toLattice` by the
  subtype. No `dist`, no axiom.
- **(D1) `d1Mayer` / `BridgeDecomposition.decompose`**
  (`Ursell4DProgress.lean:309`) — stated over the count `z4ClusterCountBound p`;
  **no `SepLattice` metric field appears at all** (its parameter is a
  `ClusterCountBound`, not a `SepLattice`).

Neither closure needs non-collapsing / directional separation; the L¹ witness
suffices for both. Directional separation is a latent requirement gated solely on
instantiating `spanning_cluster_term_le`'s `hsep` from a physical pair — not
triggered by any wired (T′)/(D1) path.

---

## 6. Named residual (the latent L∞ obligation)

The one thing L¹ does **not** provide is a metric under which a *physical*
operator pair at bridging distance `d` satisfies `d ≤ S.dist p q`. This is the
sole reason (ii) exists, and it is left as a named, currently-untriggered
Type-level residual (no `sorry`, no fake):

> **`PhysicalPairSepSupply` (LATENT, UNINHABITED).** A `SepLatticeZ4` witness
> `S` together with, for each physical bridged operator pair `(p, q)` at
> intended separation `d`, a proof `d ≤ S.val.dist p q`. The L¹ `z4Sep` cannot
> inhabit this (constant-sum pairs give `dist = 0 < d`); the L∞/BFS metric can.
> **Not on any wired path** — required only if `clusterSpanSum_decay` is
> re-routed through `spanning_cluster_term_le`.

Until that re-route happens, this residual is dead weight and the L¹ witness
`SepLatticeZ4_witness` is a complete, honest inhabitant of `(D2)` for the wired
scorecard.

---

## Evidence — relevant files (absolute)

- `/Users/darthur/Dore Dropbox/Arthur Petron/claude_folders/ym_mass_gap_sheaf/lean/YMGap/Continuum/SepLatticeZ4Close.lean` — `z4dist:96`, `edge_base_sum:83`, `z4Sep:105`, `SepLatticeZ4_witness:126`, `sPlaq_addE:131`, honest-scope note `:33–44`.
- `/Users/darthur/Dore Dropbox/Arthur Petron/claude_folders/ym_mass_gap_sheaf/lean/YMGap/Continuum/Ursell4DProgress.lean` — `TreeGraphBound:244` (touches only `.toLattice`), `BridgeDecomposition:309` (no metric field), `SepLatticeZ4:329`.
- `/Users/darthur/Dore Dropbox/Arthur Petron/claude_folders/ym_mass_gap_sheaf/lean/YMGap/Continuum/PinnedCluster.lean` — `SepLattice:234`, `dist_le_pathLen:314` (invokes only the three axioms), `connected_spanning_size_ge:347`, `toySep:250` (the faked `dist≡0` witness this improves on).
- `/Users/darthur/Dore Dropbox/Arthur Petron/claude_folders/ym_mass_gap_sheaf/lean/YMGap/Continuum/MayerClustering.lean` — `spanning_cluster_term_le:180` (defined-but-unused; only supply point that would demand `hsep`), `clusterSpanSum_decay:216` (bypasses the engine, proof `:220–221`).
- `/Users/darthur/Dore Dropbox/Arthur Petron/claude_folders/ym_mass_gap_sheaf/lean/YMGap/Continuum/Tier0Scorecard.lean` — `SubWallA:128`, `tTree:133`, `subA_tree_graph:180`, coupling note `:54–58`.

**Caller check.** `grep` over `lean/YMGap/` finds `spanning_cluster_term_le`
only in docstrings and `AXIOM_AUDIT.md` — zero proof-term applications —
confirming the "defined-but-unused" claim and, with it, that no wired path
demands directional separation.
