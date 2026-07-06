# Tier-0 Atom Status Audit (2026-07-05)

> Read-only adversarial audit of the remaining Tier-0 sub-wall atoms, prompted by
> this campaign finding two mislabeled atoms (`SixJPentagon` = a false bug; `SepLatticeZ4`
> = already closed). Build-verified: `lake build YMGapGuard` green (651 jobs), all cited
> decls `[propext, Quot.sound]`, guard reports 5 Clay-frontier types uninhabited. The Clay
> problem remains **OPEN**; this only corrects the frontier map so effort points at real work.

## The systematic structural fact (read first)

Every remaining "open atom" is a **bound on a FREE function field** (`phiT`, `offCorr`,
`racahKernel`, `gapDefect`, `shift`). Consequently:
- **None is provably-empty** like `SixJPentagon` was.
- **Each is vacuously inhabitable** by setting the function to `0`/constant.
- The genuine physics is a *semantic side-condition* (the function must be the REAL Ursell
  weight / correlator / defect) that the **types do not pin**.

So the frontier is honestly open because (a) the campaign **refuses to land the fakes**, and
(b) `YMGapGuard` forbids *unconditional landed* inhabitants of the **top-level bundles**
(`ClayTarget`, `Tier0Scorecard`, …) — **not** because the atom types are type-theoretically
impossible to inhabit. Integrity is real, but it rests on convention + the top-bundle guard,
not on atom-level uninhabitability. State this plainly in any external claim.

## Status table

| Atom | Lean type (file:line) | Class | Kind |
|---|---|---|---|
| **T′** `tree_graph` | `Ursell4DProgress.TreeGraphBound` (:244/252) | **(a) genuinely open — CHEAPEST** | finite/combinatorial |
| **D1** `decompose` | `Ursell4DProgress.BridgeDecomposition` (:309/320) | **(a) open — frontier "PROVED" is WRONG** | analytic (fixed-spacing cluster expansion) |
| **D2** `SepLatticeZ4` | `Ursell4DProgress.SepLatticeZ4` (:329) | **(b) ALREADY CLOSED** (two witnesses) | finite/geometric |
| **A2** `PentagonNumericCore` | `PentagonRelation.PentagonNumericCore` (:222) | **(c) VACUOUS / obligation ≠ physics** | algebraic (if respecified) |
| **B·Core-B** `hlocalize` | `GradedBondMovingBudget.SpectralLocalization` (:313/322) | **(a) open** = R1 `SaddleVarianceFloor` | **irreducibly analytic/continuum** |
| **B** `hbridge`/`hadd` | `AsymptoticSpectralLoc.SpectralMarginInput` (:154/159) | **(a) open** dictionary/plumbing | analytic (spectral dictionary) |

## Per-atom evidence

**T′ — genuinely open, the CHEAPEST target.** Genuine witness `TreeGraphBoundProgress.
TreeGraphReduction.toBound`, three legs:
- (A) `CubicEulerBound` — **PROVED** (`CubicEulerBoundProof.cubicEulerBound`, CubicEulerBound.lean:180).
- (P) `penroseDom` — the analytic heart is **PROVED**: `penroseIneq : |C(G)| ≤ τ(G)` for every
  graph (well-founded induction, `PenroseDomInduction.lean`). Residuals: `DCHyp`
  (deletion–contraction; delete-half definitional, contract-half = classical spanning-tree
  contraction-invariance) and `UrsellPin` (`n!·phiT = |C(adjGraph Y)|`). Pure finite `Nat`/`List`.
- (C) `cayleyMax` → `CayleyCountBound` = Cayley's `n^{n-2}` (Prüfer). Standard finite theorem.
No over-constraint / refutation found — physically correct. **The three open legs are standard
classical finite lemmas, none research-novel.**

**D1 — open; the frontier "PROVED" label is misleading.** `subA_offCorr_decompose` is a field
*accessor*, not a proof. Genuine witness `bridgeDecomposition_of_data` reduces D1 to one residual
`MayerUrsellIdentity_z4` (multi-plaquette generalization of the proved single-line
`mayerUrsell_singleLine`). Analytic (convergent polymer expansion at fixed spacing).

**D2 — already closed.** `SepLatticeZ4Close.SepLatticeZ4_witness` (L¹) + `SepLatticeZ4Linf.
SepLatticeZ4_linf_witness` (L∞). Both axiom-clean.

**A2 — vacuous as bundled.** `PentagonNumericCore` has a landed inhabitant `numericShapeWitness`
(constant `1/4`); its only constraint `smallest_value` is met by construction. The genuine physics
(real Wigner-6j solving the nonlinear Biedenharn–Elliott pentagon + stochasticity) lives in no
single non-vacuous type, and the signed `{6j}` are irrational (not `Q'`-representable). The honest
refutation content (`racahRP_fails_numeric`, `pentagonNumericCore_not_perm`) is real. **Don't
invest as stated — it is spec work, not a provable target.**

**Core-B `hlocalize` — open, irreducibly analytic.** = `CircleFourierPowerModel.SaddleVarianceFloor`
(the p≥2 SU(2)-fusion local-CLT, the sole open R1 residual `FullRangeFloor`). Research-hard.

**`hbridge`/`hadd` — open dictionary plumbing.** Constrain the free `shift`/`spacing`;
`margin_recursion_of_eigShift` is proved and discharges the old `recursion` from them. The
located-2nd-eigenvalue ↔ physical-margin dictionary + vacuum-normalized shift control; structurally
satisfiable, coupled to the Balaban-RG apparatus.

## Recommendation

1. **Attack T′ next** — the only remaining atom that is pure finite combinatorics with its analytic
   heart already proved. Three standard finite lemmas: `CayleyCountBound` (Cayley/Prüfer),
   `DCHyp` contract-half (spanning-tree contraction-invariance), `UrsellPin` (Ursell coefficient
   identity). Highest-ROI genuine open target.
2. **Do NOT invest in A2** — vacuous as bundled; needs a new correctly-specified type first, and hits
   the irrational-`{6j}` obstruction.
3. **Defer the analytic atoms** — Core-B (`hlocalize` = R1 `SaddleVarianceFloor`), D1
   (`MayerUrsellIdentity_z4`); `hbridge`/`hadd` are tractable-but-Balaban-coupled.
4. **Frontier-map corrections**: D1 is OPEN (not "PROVED"); every atom carries the free-function
   vacuity caveat above.
