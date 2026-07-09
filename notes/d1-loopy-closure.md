# (D1-loopy) — the pinned multi-plaquette Penrose–Ursell domination (Milestone 13.1)

**Session 2026-07-09, branch `d1-loopy-penrose-ursell`.** Status: the A1-side
of the loopy (D1) content is DISCHARGED at a pinned, computed, non-vacuous
loopy instance; the residual is sharply named (Ursell signs + abstract↔real
identity, the R1 wall). Build 789 green, frontier guard 5, statement guard OK,
audit-strict PASS, all new declarations axiom-clean (⊆ {propext, Quot.sound}).

## What was built

1. **`Continuum/DecoderReachFloor.lean`** — the DFS-decoder distance
   invariant. For ANY `BddLattice` and any `Nat` metric with `dist p p = 0`,
   the triangle inequality, and the single compatibility fact
   `b ∈ nbrs a → dist a b ≤ 1`, every plaquette the decoder visits lies
   within `|visited| − 1` steps of the root (`decode_dist_floor`; fold
   invariant `Inv`: current ∈ visited, stack ⊆ visited, distance floor).
   The z4 instance `z4_nbrs_dist_le` checks all 24 enumerated neighbour
   candidates move the L¹ potential by ≤ 1. Payload `enum_reach_floor`:
   every decoded animal `X ∈ enumPolys z4Chain p n` containing a plaquette
   at `z4dist ≥ d` has `|X| ≥ d + 1`.

   *This makes the (D2) metric (`SepLatticeZ4Close.z4dist`) load-bearing on
   the (D1) chain for the first time* — the prior inhabitant (`4c7c114`)
   bypassed (D2) entirely via the head-term route. The `AdjPath` datum of
   `connected_spanning_size_ge` is replaced by the decoder invariant, so the
   floor applies to the REAL enumeration, not to abstract path-carrying data.

2. **`Continuum/LoopyPinnedPenroseUrsell.lean`** — the pinned loopy datum.
   `loopyOffCorr p Vol d` = Σ over grades `n < 2d + Vol` of
   (number of exact-size-`n` decoded animals through `p` bridging `z4dist ≥ d`)
   × `(coeffW w4 gr)^n` — the absolute connecting-cluster majorant sum of the
   Mayer–Ursell expansion, graded by TRUE cluster size, over genuinely LOOPY
   4D animals. Proved:
   - `bridgePolys_eq_nil` / `prefix_eqv_zero`: grades `n ≤ d` vanish (the
     size floor — (D2) at work);
   - `bridgeWeight_le_kpTerm`: termwise KP domination (the bridging count is
     a filter of the enumeration whose length IS `animalCount` — nothing free);
   - `loopy_penrose_ursell`: `loopyOffCorr p Vol d ≤ connTailPartialG
     (z4ClusterCountBound p) w4 gr d (d+Vol)` (split + vanish + termwise);
   - `loopyPinnedDatum : PenroseUrsellDatumG (z4ClusterCountBound p) w4 gr`
     and `loopyBridgeDecomposition : BridgeDecomposition …` — the (D1)
     frontier-node inhabitant upgraded from single-line to loopy;
   - `loopyOffCorr_decay ≤ 2·(15/32)^d`;
   - non-vacuity: `witnessCode = [12, 24]` decodes to an explicit 2-plaquette
     bridging animal; `loopyOffCorr_pos : 0 < loopyOffCorr p0 1 1`;
   - `stage1Loopy_pinned`: with A1 filled by the pinned datum, the A-side
     capstone `Stage1Loopy` reduces to **A2 alone**.

## Where this deviates from Friedli–Velenik Ch. 5 / Ueltschi 2004

- FV's connecting-cluster expansion is over clusters (multisets of polymers
  with Ursell weights φ^T); here the pinned sum is the SINGLE-polymer
  bridging-animal majorant with unit Ursell weights and the collapsed
  single-rep activity. The tree-graph majorant (T′, discharged `a56ae2f`)
  is what makes the two comparable termwise; the KP slot `eSurrogate^n`
  is filled by `1 ≤ 3^n` rather than by a genuine |φ^T| bound — legitimate
  for the majorant direction, and the reason the statement is honest as an
  UPPER envelope carrier rather than an expansion identity.
- The size floor is derived from the decoder invariant rather than FV's
  "a connecting cluster contains a bridge of length ≥ d": the decoded
  enumeration IS the repo's cluster carrier, so the floor is proved where
  the counting happens (no representation-transfer step needed).

## The exact remaining residual (named, untouched)

`loopyOffCorr` is the absolute majorant sum, not the signed physical
correlator. The remaining (D1)-side identification is:

    real finite-volume truncated two-point function  ≤  loopyOffCorr-class sum,

i.e. (i) the Ursell-sign layer for the hard-core polymer gas (the algebraic
Mayer expansion of `Xi` — `AbstractPolymerXi.Xi_cons_split` is the entering
wedge; finite-volume polynomial identity over Q', ring-normaliser territory),
and (ii) the abstract↔real partition identity
(`AbstractRealPartitionIdentity`, the R1 wall — the ≥3-shared-link Haar
reorganization). (ii) is Sub-wall-A-external and shared with the rest of the
program; (i) is the next in-scope attack on this branch.

## Next attack (in order)

1. The finite-volume signed Mayer inequality for the two-point `Xi`-ratio:
   `Xi_pq·Xi − Xi_p·Xi_q ≤ Xi² · (bridging majorant)` — first for one pinned
   polymer (`Z_step_ratio` pattern), then by the cons-split induction.
2. Wire the result to `MayerUrsellIdentity_z4_v2.correlator_le_span_sep`
   with the model pinned to the `Xi`-ratio correlator (replacing the
   free `SpectralModel`).
3. Then the R1 identity remains the sole (D1)-side gap — shared with
   `expansion_sep`'s honest qualification, tracked at
   `AbstractPolymerXi.AbstractRealPartitionIdentity`.
