# (D1) Mayer–Ursell connecting-cluster expansion — audit against the fresh Ursell-pin

**File:** `lean/YMGap/Continuum/Ursell4DBridgePin.lean` (new, imported in `YMGap.lean`)
**Build:** `lake build YMGapGuard` exit 0. **Guard:** 5 Clay-frontier types uninhabited (UNCHANGED).
**Axioms:** every decl ⊆ {propext, Quot.sound}; `castBridge` needs none. No sorry/native_decide/by_contra/Classical/Real.

---

## SATISFIABILITY-FIRST verdict (the mandated check)

The (D1) atom is `Ursell4DProgress.BridgeDecomposition (z4ClusterCountBound p) w4 gr`
(the `d1Mayer` field of `FrontierDAG`). Fields: `offCorr, bridgeTerm : Nat→Q'`,
`tailLen : Nat→Nat`, `tailLen_ge`, `decompose : ∀d, offCorr d ≤ finSum (bridgeTerm (d+·)) (tailLen d)`.

1. **NOT the historical UNSAT shape.** The v1 bug `MayerUrsellIdentity_z4` was unsatisfiable
   because it hard-coded `corr := genuine SpectralModel` AND `tailLen := d`, forcing the RHS
   `clusterSpanSum` to vanish at `d=0` ⟹ zero model (`mu_z4_total_weight_le_zero`). That is
   ALREADY escaped in-repo by the free `tailLen ≥ d` in `BridgeDecomposition` and the
   `d≥1`-separated `MayerUrsellIdentity_z4_v2` (satisfiable, `diagModel`). I did not reopen it.

2. **NEW structural finding — the parameters `(cc,w,r)` are PHANTOM.** They appear in NONE
   of `BridgeDecomposition`'s fields. Machine-proved by `castBridge`: any inhabitant
   transports verbatim to arbitrary parameters. Consequences:
   - the bare type is trivially TYPE-satisfiable (`offCorr := 0`) — but VACUOUSLY;
   - it is even satisfiable by a *wrong-instance* genuine correlator (the already-discharged
     single-line `reconTransfer` at `gw=1/6`, its own envelope filling `bridgeTerm`);
   - so "discharging the bare `BridgeDecomposition` type" ≠ discharging the (D1) z4 physics.
     A bare-type inhabitant would be a Rule-6 fake. This is exactly why the repo routes the
     genuine content through the CONSTRAINED `MayerUrsellIdentity_z4_v2` (corr pinned to a
     real `SpectralModel`, RHS pinned to `clusterSpanSum (z4…) w4 gr`).

## Does the fresh Ursell-pin discharge (D1)?  NO — it is the ORTHOGONAL atom.

Split anatomy of `PenroseUrsellSplit`: `offCorr d ≤ Σ bridgeTerm ≤ Σ kpTerm`.
- **(T)/(T′)** = `bridgeTerm ≤ kpTerm` = the per-cluster tree-graph majorant `|φ^T| ≤ eSurrogate^{|Y|}`.
  This is what the Ursell-pin closes (`UrsellPinComplete.treeGraphBoundHardCore`, via K_n, |C|≤τ).
- **(D1)** = `offCorr d ≤ Σ bridgeTerm` = the PHYSICAL Mayer–Ursell expansion: the genuine z4
  connected correlator ≤ connecting-cluster sum.

The pin lives entirely on the (T) side. (D1) is the orthogonal (D) side. **The task's premise
("Ursell machinery is exactly what Mayer–Ursell needs") conflates the two sides:** the tree-graph
combinatorics is the (T′) atom that was *already* the last D-move — not (D1).

I confirmed the pin cannot be repurposed onto (D1): if you sharpen the RHS to the *genuine*
coefficient `ursellPhiTsize n = |C(K_n)|/n!` instead of the majorant `eSurrogate^n`, the folded
bridge term gets SMALLER (`ursellPhiTsize n ≤ eSurrogate^n`), so the physical bound
`corr ≤ Σ kpTerm` no longer suffices. The `eSurrogate^n` majorant is precisely the room the
physical bound needs — so the genuine `bridgeDecomposition_of_data_v2` keeps `bridgeTerm := kpTerm`.

## The exact resisting lemma (named sharply)

`MayerUrsellIdentity_z4_v2.correlator_le_span_sep` — for a genuine z4 `SpectralModel model`,
`∀ d≥1, corr model d ≤ clusterSpanSum (z4ClusterCountBound p) w4 gr d`. Re-exposed as
`physical_bound_is_the_open_field`. Its constructive proof needs (D2) `SepLatticeZ4` (to run
`connected_spanning_size_ge` on the z4 correlator's own cluster expansion) + the multi-plaquette
expansion identity — NOT the tree-graph combinatorics. LEFT UNINHABITED.

## Genuine machine-checked content landed (reusing the fresh machinery, non-vacuous)

| decl | content |
|---|---|
| `castBridge` | phantom-parameter proof (the under-constraint) — **0 axioms** |
| `ursellPhiTsize`, `_nonneg`, `_le` | per-size (T′): `\|C(K_n)\|/n! ≤ eSurrogate^n` via the FRESH pin chain (`penroseIneqConst (-1)` + `cayleyLooseBound_closed` + `legA_loose cubicEulerBound` + reciprocal cancel `ofNat_mul_mkPos_recip_eqv`). Genuine (=1/2 at n=2), the (T) side the pin covers |
| `bridgeDecomposition_of_physical` | genuine (D1) reduction to the single physical field (re-exposes `bridgeDecomposition_of_data_v2`) |
| `physical_bound_is_the_open_field` | the exact resisting lemma pinned |

## Bottom line (HONEST)

**(D1) is NOT discharged; it is NOT the second Category-A D-move via the Ursell-pin.** The pin
already discharged the neighbouring atom (T′) (the tree-graph majorant, (T) side, per-size form
re-proved here). (D1) is the orthogonal PHYSICAL Mayer–Ursell expansion whose sole open content
is `correlator_le_span_sep` — needing (D2)+multi-plaquette expansion, not the pin. The bare
`BridgeDecomposition` type is under-constrained (phantom params), so bare-type satisfiability is
vacuous; the genuine constrained target stays uninhabited. Guard stays 5. Fixed spacing
(ρ4=15/32); NOT the continuum modulus; Clay YM gap OPEN.
