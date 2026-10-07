# Scope: Z4 polymer KP on the periodic 4-torus (2026-10-07)

**Status: IMPLEMENTED** (`lean/YMGap/Continuum/Z4TorusPolymerKP.lean`, 110 lines, plus a
generalisation of `Z4PolymerKP` to any `BddLattice` with `D = 24`).  This is
**GROUP-BLIND PLUMBING** (U(1) rule): it is not gap evidence by itself.

## 1. Inventory (before this note)

### `Z4TorusGeometry`
- `wrapSucc`, `wrapPred`, `tAdd`, `tSub`, `InBox`; `tSub_tAdd` / `tAdd_tSub` / `tSub_ne` (for `2 ≤ N`).
- `torusPlaquettes` (= `boxPlaquettes`), with `_length` = 6N⁴, `_nodup` and `mem_`.
- `torusLinks`, with length 4N⁴ and nodup.
- `torusEdgesOf`: the four wrap-around links of a plaquette.
- `incidentPlaqs N ℓ`: 6 entries; `incidentPlaqs_nodup` for `2 ≤ N`.
- Incidence lemmas: `filter_sub_incident`, `incident_sub_filter`, and
  `torus_link_incidence_eq_six` (for `2 ≤ N`, exactly 6 plaquettes per link).
- Translations: `tShift`, `torusEdgesOf_shift`.
- Embedding of the free box: `box_mem_torus`, `box_torusEdges_eq`.

### `TorusWilsonAction`
- `invShift`, `shiftPlaq`, `torusPlaquettes_shift_perm`.
- `holonomy`, `wilsonAction`, `wilsonAction_shift_invariant`.

### `TorusGaugeInvariance`
- `gaugeTransform`, `holonomy_gauge`, `wilsonAction_gauge_invariant`.

### `TorusSlabInsertion` / `TorusSlabCover`
- Slabs: `slabTimes`, `crossSection`, `slabVertices`, `slabPlaquettes`.
- `slab_disjoint`, `slab_cover`, `slab_partition_perm`.

### SU(2) torus files
- `SU2TorusWilsonGibbs`: `ConfigHaar`, `LinkHaar`, `chi`, `charWeight`, `SU2Schur`, `partition`,
  `numerator`.
- `SU2TorusPolyGibbs`: `PolySchurUpTo`, `partition_constructed`.
- `SU2TorusSchurSmall`: `pairing_*`, `polySchurUpTo2`.

### What was missing
There was **no torus plaquette neighbour list and no torus `BddLattice`**. The only
`BddLattice` instances were `zChain` and `z4Chain` (the corner-anchored box ℤ≥0⁴).

## 2. Torus plaquette graph and degree

### Definitions
- `torusBoundary N p ℓ := inBoxB N p.1 && ℓ ∈ torusEdgesOf N p`. Off-box plaquettes carry no
  links, so they are isolated vertices of the graph.
- `torusNbrs N p := (torusEdgesOf N p).flatMap (incidentPlaqs N)`.

### Proved in Lean
- `torusNbrs_length`: the list has length exactly 24 for **every** N.
- `torus_sound`: every link-adjacent plaquette appears in the list. Hence
  `torusChain N : BddLattice` with `D = 24`.

The list always contains `p` itself 4 times. This matches the box `z4Nbrs`.

### Distinct entries (computed by an exhaustive Python check at the origin, not proved in Lean)

| side N | list length | distinct | distinct ≠ p | list = true adjacency set |
|---|---|---|---|---|
| 1 | 24 | 5 | 4 | yes |
| 2 | 24 | 19 | 18 | yes |
| 3 | 24 | 21 | 20 | yes |
| 4 | 24 | 21 | 20 | yes |

- **N = 1:** all wraps are trivial. There are only 2 distinct links and 6 plaquettes in total.
- **N = 2:** `v+e = v−e`, so the two coplanar neighbours in each in-plane direction coincide.
  Each of them shares two links with p.
- **N ≥ 3:** the true simple degree is 20, the same as the bulk of ℤ⁴.

The count needs only the upper bound `≤ 24`, so small sides are covered too. They are merely
over-counted. **No lemma for side ≥ 3 is needed.** A distinctness lemma for N ≥ 3 (20 distinct
neighbours) is not proved. It would only sharpen the constant.

## 3. Does the 625ⁿ spanning-tree count transfer?

Yes, verbatim. `AdjSpanningBuild.clusterCountBound_animal` and `animalCount_le_pow` are
generic in the `BddLattice`. They use only `deg_le` and `adjacent_mem_nbrs`; no geometry
enters. `torusClusterCountBound_animal N p` instantiates the count at K = (24+1)² = 625.

For this, `Z4PolymerKP` was generalised. The theorems below now take `(hD : BL.D = 24)` and a
default plaquette `d`:
- `shareB`, `firstIn`, `group_le`, `pigeon`, `class_sum`, `Z4BoxGas BL`, `z4_hgroup`;
- `deg24_kp`, the main theorem.

`z4_kp` keeps its old statement (`Z4BoxGas z4Chain`) as a one-line wrapper.

`torus_kp N B z hz1` gives the same three conclusions on `torusChain N`, unconditionally, for
**every** N, with ε = 1/10000 and η = 1/2500:
- Ξ ≥ 0;
- the removal ratio;
- 1 ≤ Π(1+η^{|X|})·Ξ.

## 4. Winding polymers

A connected animal of size ≳ N can close a non-contractible cycle, for example a tube of
plaquettes wrapping one direction.

- **For KP: no special handling.** `torus_kp` quantifies over all connected animals,
  winding ones included.
  - The per-plaquette count bounds the number of animals through a plaquette by the
    degree alone (625ⁿ), whatever their topology.
  - Winding animals have size ≥ N (roughly ≥ 4N for a closed tube), so their weight is at
    most ε^N. That is exponentially small in the side length.
- **For the physics, they matter. Flag:** the KP bound treats the Wilson-action polymer gas
  with free activities. It does **not** see:
  - centre-symmetry sectors;
  - Polyakov loops: the expectation of a Polyakov loop is dominated by
    winding polymers of size ~N;
  - the temperature direction: a short time direction gives deconfinement at finite T.

  A torus mass-gap or confinement argument must separately treat:
  - observables supported on winding cycles;
  - activities on a torus with an asymmetric side L_t ≪ L_s.

  `torusChain` uses one common side N, so it is a **symmetric torus only**.

## 5. Lean work and what remains

### Done
- **About 110 lines:** `Z4TorusPolymerKP.lean`.
- **About 30 changed lines:** the parametrisation of `Z4PolymerKP`.

### Open (estimates)
- **About 120–200 lines:** an asymmetric torus (L_t ≠ L_s). This needs `tAdd` with a
  per-direction side, and `Z4TorusGeometry` is single-N.
- **About 80 lines:** the N ≥ 3 distinctness lemma (20 neighbours). It would allow K = 21².
- **Not started:** a torus Wilson-gas activity bound tying `wilsonAction` to `z`. This is
  the real physics link.
