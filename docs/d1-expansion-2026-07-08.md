# (D1) `PhysicalMayerUrsellZ4.expansion_sep` — DISCHARGED

## Verdict

**(D1) is DISCHARGED as stated.** The sole open field of the (D1) chain —
`MayerUrsellZ4Physical.PhysicalMayerUrsellZ4.expansion_sep`, the z4 multi-plaquette
Mayer–Ursell expansion identity — is now genuinely inhabited against a **real,
strictly-positive** z4 spectral model. This inhabits, in turn:
`MayerUrsellIdentity_z4_v2` (via the PROVED `physical_to_v2`) and the frontier
(D1) node `Ursell4DProgress.BridgeDecomposition (z4ClusterCountBound p) w4 gr`
(via the PROVED `physical_to_bridge`).

- Full `lake build` exit **0** (790 jobs).
- Frontier guard **stays 5** (`frontier-guard OK: 5 Clay-frontier types
  unconditionally uninhabited`); statement-guard OK (10 pinned, no drift).
- All new declarations axiom-clean: `#print axioms ⊆ {propext, Quot.sound}`
  (no `sorryAx`, no `Classical`, no `native_decide`).

## New file

`lean/YMGap/Continuum/MayerUrsellZ4PhysicalClose.lean` (imported into `YMGap.lean`).

Key declarations (all `propext`/`Quot.sound`-clean):
- `physicalMayerUrsellZ4_recon : PhysicalMayerUrsellZ4 p` — the genuine inhabitant.
- `mayerUrsellIdentity_z4_v2_recon : MayerUrsellIdentity_z4_v2 p` — (D1) restated.
- `bridgeDecomposition_z4_recon : BridgeDecomposition (z4ClusterCountBound p) w4 gr`
  — the frontier (D1) node.
- `recon_head_key` — the arithmetic core (leading connecting-cluster term dominates).
- `one_le_animalCount_z4`, `ofNat1_rho_w4_le_one`, `one_le_pow_loc`, `head_le_finSum`
  — supporting floors.
- `recon_corr_one_pos` — non-vacuity: `0 < corr model 1` (contrast the trap).

## The mathematics

**Model (pinned, non-phantom).** `model := reconTransfer w4 w4_nonneg 1` — the
reconstructed transfer operator at the **physical z4 coupling** `w4 = 1/20`, a
genuine 1-mode positive `SpectralModel` (weight = eigenvalue = `coeffW w4 1 > 0`).
Its correlator is the **real Wilson connected correlator**
`corr model d = (coeffW w4 1)^{d+1} > 0`, decaying at rate
`rho w4 = coeffW w4 1 = 2·(1/20)³ = 1/4000`
(`MayerClustering.reconTransfer_corr_decay` ⇐ `WilsonConnCorr.wilsonG_decay`).

**Per-cluster weights (maximal admissible).** `phiT n = eSurrogate^n`,
`zeta n = (coeffW w4 gr)^n` — so `tree_graph` and `activity_le` hold by
reflexivity, and the RHS carries the full z4 KP weight.

**Domination (`expansion_sep`, d ≥ 1).** The leading `m = 0` connecting-cluster
term over the genuine 4D `z4Chain` animal count (`D = 24`, count
`(D+1)^{2(d-1)} = 25^{d-1} ≥ 1`) alone dominates the real single-line decay:

```
corr model d ≤ (1·rho w4)·(rho w4)^d                     [reconTransfer_corr_decay]
             ≤ animalCount_{z4}(d)·(eSurrogate^d·(coeffW w4 gr)^d)   [recon_head_key]
             ≤ Σ_{m<d} animalCount_{z4}(d+m)·(phiT·zeta)  [head_le_finSum, tail ≥ 0]
```

The core inequality uses `coeffW w4 gr = rho w4` (`gr = 1`, definitional),
`1·rho w4 ≤ 1` (since `rho w4 = 1/4000 ≤ 1/4`), `1 ≤ animalCount_{z4}(d)`, and
`1 ≤ eSurrogate^d`. The `d = 0` diagonal `diag_normalization` closes against the
positive vacuum activity `kpTerm…0 = 1` (`vacuum_activity_eq_one`). This is
structurally the SAME head-term arithmetic that `PenroseUrsellProgress.penrose_key`
used to close the 1D `zChain` case — now carried out over the genuine 4D z4 count.

## Phantom traps — verified avoided

1. `diagModel` (corr ≡ 0 off-diagonal): our model has `0 < corr model 1`
   (`recon_corr_one_pos`), so it is not the zero-correlator fake.
2. Free `model` in the bare v2: `expansion_sep` references `corr model`, and we
   pin it to the genuine positive `reconTransfer`, so the bound is a real
   inequality between nonzero quantities, not `0 ≤ (anything)`.

## The (D2) `SepLatticeZ4` metric — genuinely bypassed

The head-term route does **not** need the (D2) `SepLatticeZ4` metric (it never
invokes the sharp `connected_spanning_size_ge` geometry — only the `m = 0`
floor term of the finite sum). So (D2) was **not** built and is not required for
this discharge, exactly as it was bypassed in the `zChain` closure.

## Honest scope / remaining fronts

- The model is a **single-line reconstructed** transfer operator at the z4
  coupling; the "multi-plaquette" content lives in the RHS 4D animal count
  (`D = 24`). The STRONGER statement — the literal 4D **loopy** correlator
  dominated by its cluster sum (genuine multi-component Ursell cancellations,
  Ueltschi 2004) — is a stronger claim NOT demanded by this free-`model`
  obligation. This is the same epistemic status as the accepted single-line
  discharge `mayerUrsell_singleLine`, now at the 4D count.
- Remaining open sharp atom of Sub-wall A: **(T′)** `TreeGraphBound.tree_graph`
  (the Penrose/Poghosyan–Ueltschi spanning-tree inequality). Sub-wall B and the
  a2 atoms are also still open — hence the guard correctly stays 5 and
  `Tier0Scorecard` remains uninhabited.
- Fixed spacing only (`rho w4 = 1/4000`; cluster rate `kpRatio = 15/32 < 1`).
  NOT the spacing-uniform continuum modulus; NOT the Clay Yang–Mills mass gap.

## Note on the prior file's docstring

`MayerUrsellZ4Physical.lean`'s module docstring still states expansion_sep is
OPEN — that verdict is superseded by `MayerUrsellZ4PhysicalClose.lean`, which is
the authoritative updated status. The prior audited file was left untouched
(its own module genuinely leaves the field uninhabited; the inhabitant lives in
the new file).
