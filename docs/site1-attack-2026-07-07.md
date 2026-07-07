# SITE-1 attack — the intra-block per-MOVE decomposition of `singleStep`

**Date:** 2026-07-07.
**Lean deliverable:** `lean/YMGap/Continuum/SITE1PerMoveDefect.lean` (new, imported in `YMGap.lean`).
**Build:** full `lake build` GREEN; `YMGapGuard` = **frontier-guard OK: 5 Clay-frontier types uninhabited** (unchanged). `#print axioms` on all 9 gated decls ⊆ `{propext, Quot.sound}` (`additive_perMove_insufficient` is axiom-FREE). No `Classical.*`, `native_decide`, `sorry`, `ring`.

---

## VERDICT (machine-checked): (iii) HONEST COLLAPSE

**SITE-1 does NOT move `F` below `singleStep`.** The finer per-MOVE scale — the single place in the 741-node tree the master map flagged as the one ledger-legal chance to move `F` below the atomic core — **equi-inhabits `singleStep`**. The concentration lever (`ρ_m < m·ρ_1`) that could have made a per-move object strictly weaker is a **joint/multi-move property, not a per-move sum**, and the additive per-move fold reconstructs the linear-in-`m` wall, strictly too weak for the block quadratic. `F` stays 1; `D` stays 0; guard stays 5.

This is task criterion **(iii)** — a genuine negative, NOT a `:= SingleStepDefectBound` alias (`PerMoveDefectBound` is a distinct multi-field structure; the collapse is *proved*, not declared).

---

## What was built and PROVED

### 1. The FREE per-move fold (composition is free — genuinely proved)
- `blockProd` — the intra-block survival **product** `∏_{j<m} σ_j` (the `codyFloor` multiplicative dual of `CodynamicCore.nBound`/`nstep_d`; for a *margin* the free Grönwall bound is the survival product, not the additive `Σδ`).
- `fold_margins` (axiom-free up to `propext`) — the n-step transition: from the per-MOVE recursions `σ_j·μ_j ≤ μ_{j+1}` (survivals `σ_j ≥ 0`) it folds to `(∏σ_j)·μ_0 ≤ μ_m`. No linearity, no margin-nonnegativity consumed. This is the "composition is free" half.

### 2. The honest per-MOVE object `PerMoveDefectBound`
Carries the SAME true-margin flow one scale finer: `m` moves per block, per-move survivals `moveSurv k j`, a finer per-move margin chain `fineMargin k j` pinned at the block endpoints, the atomic per-MOVE recursion `moveStep` (one single bond-move's degradation, the `coeffW_dev`/`bondMovingDelta` seed), and the `blockAssembly` linking the product of per-move survivals to the block factor `(1 − δ_block)`.

### 3. The two maps ⟹ EQUI-INHABITATION (the collapse)
- `singleStep_of_perMove : PerMoveDefectBound → SingleStepDefectBound` — the FREE fold direction (`fold_margins` + `blockAssembly`), works at **arbitrary** `m`.
- `perMove_of_singleStep : SingleStepDefectBound → PerMoveDefectBound` — the COLLAPSE witness: a GENUINELY multi-move (`m = 2`) per-move structure built from any `singleStep` by the **island-loaded** scheme (`CodynamicHierarchical.exactLoss = 0`): move 0 carries the whole block defect (`σ = 1 − δ_block`), move 1 is FREE/exact (`σ = 1`). Move 0's recursion IS `singleStep`; the free move is `1·μ ≤ μ`; the block-assembly is the product identity `(1·(1−δ))·1 ≃ 1−δ`.
- `site1_perMove_equiinhabits` = the `Type`-level pair of both maps.

**Not a dodge:** the collapse witness is `m = 2` (genuinely multi-move), and move 0 carries the REAL block defect `1 − δ_block` — it is NOT a `δ_move := 0` / model dodge. The fold in the forward map is general over the structure's free `m` field.

---

## Why the CONCENTRATION escape fails (maximal adversarial guard — machine-refuted)

The candidate strict-weakness lever was `ρ_m < m·ρ_1` (`MultiLinkFusionDefect.selfFusion_subadditive`): the m-fold fusion concentrates, so a per-move sum could sit strictly below the block. Refuted two independent ways:

1. **`additive_perMove_insufficient` (axiom-free `decide`).** The RAW single-move seed is `bondMovingDelta w 1 ≤ 6(1 − w)` (`perMove_raw_envelope` = `bondMovingDelta_to_zero` at `p = 1`, `K(1) = 6`). The additive `nstep_d` / union-bound fold over `m = 8` moves (`p = b³`, `b = 2`, `d = 4`) gives `6m(1 − w)` — the **linear-in-m semigroup wall** (`InteractingMFoldDefect`: `2 − ρ^free_m = 6mε`, NOT the concentrating fusion `6ε/m`). At `w = 1/2`: additive = `24`, block quadratic `6(1 − w)² = 3/2`, and `¬(24 ≤ 3/2)`. So the additive per-move fold does **not** reach the block bound — the concentration that makes the block quadratic is joint, not a per-move sum. Hence the ONLY per-move object that *implies* `singleStep` is one carrying the block-assembly product, which equi-inhabits.

2. **`singleStep_satisfiable_zero` / `singleStep_falsifiable`.** The per-move raw envelope is a fusion/`afr`-only fact (no `trueMargin`), TRUE for every `afr`, whereas `singleStep`'s truth VARIES with `trueMargin` at fixed `afr` (holds at `tm ≡ 0`, fails at `tm = (1,0,…)` because `δ_0 ≤ 1/2`). So no `afr`-only per-move envelope can determine `singleStep` (mirrors `SingleStepDecompositionAdjudication`).

`site1_escapes_refuted` bundles both; `site1_verdict` bundles the whole adjudication (collapse pair `×` escape refutations).

---

## The logical dichotomy (the crux, stated sharply)

Any candidate per-move object is exactly one of:
- **too weak to imply `singleStep`** — the additive/afr-only per-move envelope, which sums to the linear-in-m wall `6m(1−w) ≫ 6(1−w)²` (refuted escape #1); or
- **equi-inhabiting `singleStep`** — any per-move object strong enough to fold up must carry `blockAssembly`, which is satisfiable *from* `singleStep` by the island-loaded witness (`perMove_of_singleStep`).

There is **no strictly-weaker-AND-implying** per-move object. The concentration `ρ_m < m·ρ_1` is genuine physics but supplies the SAME logical strength, not a weaker computable F-node. The per-move scale is therefore a COLLAPSE, closing the last codynamic hope the master map identified.

---

## Honest scope

- Nothing is inhabited unconditionally: every producer is an open binder (`P : PerMoveDefectBound` or `S : SingleStepDefectBound`). Guard correctly stays at 5.
- `singleStep` remains the atomic Clay core (`F = 1`, status 2). No 4D Yang–Mills mass gap claimed.
- Anti-loop: this is criterion (c) — REFUTE a genuinely-live candidate route (the per-move SITE-1 route). NOT a `C++` alias (no `def X := SingleStepDefectBound`).
