# Structural adjudication — the multi-plaquette "degeneracy-resummation" residual

**File:** `lean/YMGap/Continuum/ResummationAdjudication.lean` (new; imported in `lean/YMGap.lean` after `MultiPlaquetteEffectiveTransfer`).
**Build:** full `lake build` GREEN (755 jobs). **Guard:** `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`.
**Axioms:** every load-bearing decl `[propext]` / `[propext, Quot.sound]`; `resummation_gap_is_dimQ`, `resummed_margin_not_uniform` axiom-free. NO `sorryAx`, NO `Classical`, NO `native_decide`, NO `ring`/`nlinarith`. `decide` only on closed rationals (`1 < dimQ 1`; the two non-uniformity witnesses).
**No `:= SingleStepDefectBound` alias** — progress metric `C = 18` UNCHANGED, `F = 1`, `D = 0`, guard = 5.

---

## DEFINITIVE VERDICT

**The resummed-clustering residual EQUI-INHABITS the atomic core `singleStep` — it is a sharp, numerically-pinned RE-FRAMING (factor `dimQ 1 = 2`, `2w³` vs `w³`), NOT a strictly-weaker `F`-node below the core. `F = 1` STANDS. The multi-plaquette construction did NOT move the core.**

It is neither (a) a free/computable heat-kernel fact (the free/naive transfer provably VIOLATES it — machine-checked refutation), nor (b) a strictly-weaker sub-obligation of `singleStep` (it is transfer-side/single-scale, incomparable to the `tm`-recursion by the same `tm`-independence argument that demoted `uniform_in_m`), nor (c) a core-bypassing parallel obligation (its per-scale margins are lattice-units and vanish as `w→1`, so it does not supply the uniform physical floor that `singleStep` provides).

---

## 1. The residual, formalized precisely (`ResummedClustering`)

The EXACT standalone content of the hypothesis of `MultiPlaquetteEffectiveTransfer.fullWindow_gap_of_resummed_clustering`, over the REAL block correlator (a supplied `SpectralModel`), not a model:

```lean
structure ResummedClustering (S : SpectralModel) (w : Q') : Type where
  amp      : Q'
  amp_pos  : 0 < amp
  cluster  : ∀ n, corr S n ≤ amp * (heatKernelSep w) ^ n     -- clusters at RESUMMED rate w³
  coupled  : ∀ i, i < S.k → 0 < S.w i
  dead     : ∀ i, S.k ≤ i → S.lam i ≤ heatKernelSep w
```

This is "the real block-spin transfer's correlator clusters at `w^{C₄}=w³` (degeneracy as multiplicity) rather than `dimQ·w^{C₄}=2w³` (degeneracy compounding per link)". `Type`-level (Rule 8; the amplitude is data).

## 2. DIRECTION A — the producer (PROVED)

`gap_of_resummedClustering : ResummedClustering S w → LocatedSpectralGap S` (for `0<w<1`), separator `heatKernelSep w = w³`. Margin strictly positive: `resummedClustering_gap_margin_pos : 0 < 1 − sep = 1 − w³`. So the residual genuinely PRODUCES a located gap on all of `(0,1)`. **Direction A holds.**

Non-vacuity: `resummedClustering_effTransfer` — the block-spin MODEL `effTransfer` INHABITS `ResummedClustering` (exactly the proved `eff_corr_cluster` + `coeffW_pos` + `effLam_le_sep`). The predicate is satisfiable; the resummed model realizes it.

## 3. DIRECTION B — the crux: EQUI-INHABITATION, not strict-weakness

### 3a. The residual is NON-FREE (the physics check, PROVED refutation)

`reconTransfer_not_resummedClustering` — for every `0<w<1`, the NAIVE per-plaquette (degeneracy-COMPOUNDING) real single-edge correlator `reconTransfer` — the genuine Wilson correlator (`wilsonG_eqv_reconTransfer_corr`) — **provably VIOLATES `ResummedClustering`**. Proof: a witness would (Direction A) force a located gap at `sep = w³`, hence the leading eigenvalue `coeffW w 1 = dimQ 1·w³ = 2w³ ≤ w³`, contradicting `w³ < 2w³` (from `0 < w³`).

This is decisive for the physics check the task posed. The resummed rate `w³` is the free heat-kernel VALUE, but **achieving it is NOT a free fact**: the free/naive transfer gives `2w³` and fails the predicate. Whether the REAL interacting block transfer resums the degeneracy `2w³ → w³` is precisely the interacting block-spin effective-action question — the SAME non-perturbative content as `singleStep`'s `realδ ≤ δ_model`. There is no reflection-positivity or free shortcut: RP gives self-adjointness/positivity (eigenvalues in `[0,1]`), not the value of the second eigenvalue.

Numerically pinned (sympy-exact / mpmath dps=50):

| `w` | resummed `w³` | naive `2w³` | naive ≥ 1 (no free gap)? | above `w*≈0.7937`? |
|---|---|---|---|---|
| 4/5 | 0.512 | 1.024 | yes | yes |
| 9/10 | 0.729 | 1.458 | yes | yes |
| 99/100 | 0.970299 | 1.940598 | yes | yes |

`resummation_gap_is_dimQ` (axiom-free): `coeffW w 1 = dimQ 1 · heatKernelSep w` exactly — the two rates differ by the fixed rep degeneracy `dimQ 1 = 2`, and `coeffW w 1 − heatKernelSep w = w³ > 0`. The residual is exactly this factor-`2` identity.

### 3b. The residual is INCOMPARABLE to `singleStep` — not a strictly-weaker sub-obligation

`ResummedClustering S w` is a single-scale, transfer-operator-side statement that **does NOT mention the true margin `tm`**. `singleStep`'s truth VARIES with `tm` at fixed `afr`:

`resummedClustering_is_transferSide_not_singleStep` (reusing the imported `singleStep_satisfiable_zero` for `tm≡0` and `singleStep_falsifiable` for a concrete `tm`) certifies both. Hence — verbatim the argument that demoted `uniform_in_m` in `SingleStepDecompositionAdjudication` — no transfer-side / `afr`-only statement can imply or be equivalent to the `tm`-recursion `singleStep`. So `ResummedClustering` is INCOMPARABLE to `singleStep`, not a strictly-weaker sub-obligation of it (for an `F`-move BELOW the core one needs `singleStep → piece` with the piece strictly weaker; here neither implies the other).

### 3c. The residual does NOT bypass `singleStep` to the physical floor

`resummed_margin_not_uniform` (decidable): the per-scale margin `1 − w³` is positive but DECREASES toward `0` as `w→1` (smaller at `999/1000` than at `99/100`). So the multi-plaquette per-scale located gaps are in LATTICE units and do NOT deliver the uniform PHYSICAL continuum floor — that still requires the `tm`-recursion `singleStep` (via `DefectGapRecursion`). The resummed route is a per-scale gap producer, not a replacement for the core.

## 4. The bundled verdict theorem

`resummation_adjudication_verdict` machine-checks, for all `0<w<1`:
1. `ResummedClustering` produces a located gap with margin `1−w³ > 0` (Direction A);
2. the naive per-plaquette real transfer `reconTransfer` violates it (non-free);
3. at every `afr`, `singleStep` is satisfiable AND falsifiable in `tm` (transfer-side incomparability).

## 5. Consequence for the `F` counter

- `F = 1` (atomic `singleStep`) STANDS — validated, not moved.
- `C = 18` unchanged (no alias emitted; `ResummedClustering` is a distinct predicate with a producer, a refutation, and independence proofs — the SITE-1 / SingleStepDecomposition template, not a `:= SingleStepDefectBound`).
- `D = 0`, guard = 5 (nothing discharged).
- Ledger status: the multi-plaquette construction is a genuine per-scale CONSTRUCTION INCREMENT (located gaps on all `(0,1)` in lattice units), but its residual `ResummedClustering` EQUI-INHABITS the atomic core. Spawning further attacks whose predicted outcome is "the real transfer resums to `w³`" is now provably the same interacting content as `singleStep` — a loop under the anti-loop rule.

The only honest attacks remain (a) prove atomic `singleStep` directly (construct/bound the real 4D block-spin per-step defect over the full RG recursion) or (b) a genuinely-new strictly-weaker reduction (none known). `SingleStepDefectBound` inhabited nowhere; the 4D Yang–Mills mass gap remains OPEN.

## Axiom gate (from `#print axioms`)
```
gap_of_resummedClustering, resummedClustering_gap_margin_pos,
resummedClustering_effTransfer, reconTransfer_not_resummedClustering,
resummedClustering_is_transferSide_not_singleStep,
resummation_adjudication_verdict                         : [propext, Quot.sound]
resummation_gap_is_dimQ, resummed_margin_not_uniform     : (no axioms)
```
