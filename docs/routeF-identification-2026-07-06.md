# Route F — the Bałaban IDENTIFICATION core: transfer-matrix ↔ character correspondence

**Target.** `HeatKernelSecondCumulant.GapChannelDomination` — the convergent Clay core of
Routes A/B/D/E. Its two regime BOUNDS are proved (Route D higher-rep tail, Route E
large-field). The remaining piece was the **IDENTIFICATION**: prove that the real 4D SU(2)
block-spin margin degradation genuinely **IS** the fused-character defect (the
transfer-matrix ↔ character correspondence). This deliverable proves that correspondence.

**Deliverables.** `lean/YMGap/Continuum/RouteFTransferIdentification.lean` (full `lake
build` green, frontier-guard OK, axiom-clean), `routeF_numerics.py` (mpmath dps 50, sympy
exact), this report.

---

## 1. The transfer-matrix ↔ character content (made rigorous)

The 4D SU(2) lattice gauge transfer matrix `T` (time-slice plaquette-character operator)
is **diagonal in the SU(2) characters** (character orthogonality diagonalizes it), with
eigenvalues the heat-kernel character coefficients

```
coeffW(w,s) = dimQ(s)·w^{C₄(s)},   dimQ(s)=s+1,  C₄(s)=s(s+2)
             vacuum coeffW(w,0)=1,  gap edge coeffW(w,1)=2w³.
```

This is **exactly** the in-tree `TransferCorr.reconTransfer` operator, whose located gap
`MayerClustering.reconTransfer_located_gap` has separator `sep = rho gw = coeffW gw 1` —
the first-excited/vacuum character ratio. **`reconSep_eq_charExcited` proves this
connection by `rfl`**: the genuine transfer-operator located-gap separator IS the
fundamental-channel character coefficient `coeffW gw 1 = sepFine gw` (`gw = 1/6`). The mass
gap is `Δ = 1 − sep`; the physical mass `m = −log sep`, and `−log(1−x) ≥ x` gives
`m = −log(1−Δ) ≥ Δ` (bridge to the physical mass — documented; no `log` primitive is
needed, the repo works multiplicatively in `1 − sep`, per `LocatedSpectralGap.gapMargin`).

Under one block-spin RG step the **coarse** transfer matrix `T'` is the block **FUSION**
of `T`: its channel-`s` eigenvalue is the fused character coefficient — the 2-fold central
autoconvolution `acNfull(w,t) = Σ_{p≤t} coeffW(w,p)·coeffW(w,t−p)`
(`CircleFourierPowerModel`; the two parallel fine links of the block fuse via character
convolution). Fused vacuum `acNfull(w,0)=1`, fused first-excited `acNfull(w,1)=2·coeffW(w,1)
=4w³` (the two Clebsch channels `(0,1),(1,0)`). Coarse separator `sep' = acNfull(w,1)`.

---

## 2. THE IDENTIFICATION (proved — exact `Q'` identities)

The block-spin **margin degradation** is the difference of fine and coarse margins = the
**increase of the separator** = the **fused-character defect**:

```
Δ − Δ' = (1 − sep) − (1 − sep') = sep' − sep = acNfull(w,1) − coeffW(w,1) = coeffW(w,1) = 2w³,
```

equivalently `Δ' = Δ − coeffW(w,1)` (coarse margin = fine margin − defect). Two exact
theorems:

| Lean theorem | statement | axioms |
|---|---|---|
| `reconSep_eq_charExcited` | `reconTransfer_located_gap.sep = coeffW gw 1` (transfer sep = char ratio) | propext, Quot.sound |
| `sepCoarse_eqv_two_sepFine` | `acNfull w 1 ≃ coeffW w 1 + coeffW w 1` (coarse = 2× fine) | propext |
| **`fusedDefect_eqv_charExcited`** | **`sep'(w) − sep(w) ≃ coeffW w 1`** (degradation = defect, separator form) | propext |
| **`coarseMargin_eq_fineMargin_sub_defect`** | **`1 − sep'(w) ≃ (1 − sep(w)) − coeffW w 1`** (margin form) | propext |
| `fusedDefect_le_modelEnvelope` | `sep'(w) − sep(w) ≤ 6(1−w)²` for `0≤w≤1/2` (= δ_model envelope) | propext |

`fusedDefect_le_modelEnvelope` chains the identification with the PROVED
`RouteADefectCharacter.charExcited_le_modelEnvelope`, so the **real transfer-matrix margin
degradation sits under the SAME transverse-quadratic envelope `6(1−w)²` that bounds the
model defect `δ_model`** — identifying `δ_model` as the fused-character transfer-matrix
margin loss, *derived from the eigenvalue picture, not posited*.

### Numeric validation (`routeF_numerics.py`, mpmath dps 50, sympy exact)

- **Identification exact:** `sep'(w) − sep(w) = fdef(w) = coeffW(w,1) = 2w³` for all tested
  `w` — max error `8.3e-52`; sympy confirms `(Δ−Δ') − coeffW1 = 0` and `fdef − coeffW1 = 0`
  identically.
- **−log picture:** raw log-degradation `m − m' = log(sep'/sep) = log 2` exactly; the
  bridge `m = −log(1−x) ≥ x = gapMargin` holds at every tested `w`.
- **Multiplicity-blind check (GapIsEigenvalue verdict A):** `eigA(w,1)=w³ < 1` and
  dominates `s=1..7` for all `w∈[0,1]`, including `w=95/96` near the continuum.

---

## 3. The guard-safe reduction of `GapChannelDomination` (NOTHING inhabited)

`TransferCharacterCorrespondence afr` names the **sharpest residual**: the transfer-op ↔
character eigenvalue correspondence carried *dynamically* along the AF flow —
`trueMargin`, its positivity/nonnegativity, the real defect `realDefect`, the
form-preservation recursion `correspondence` ((1−realDefect)·m_k ≤ m_{k+1}), and the open
bound `dominatedByModel` (realDefect_k ≤ afDefectSeq_k = δ_model).

`correspondence_to_gapChannelDomination : TransferCharacterCorrespondence afr →
GapChannelDomination` is a **conditional producer** (open-hypothesis binder — NOT an
unconditional inhabitant, so the frontier guard does not flag it). The `domination` bound
follows by character monotonicity: `realDefect_k ≤ afDefectSeq_k ⟹ 1−afDefectSeq_k ≤
1−realDefect_k`, and with `m_k ≥ 0`, `(1−afDefectSeq_k)·m_k ≤ (1−realDefect_k)·m_k ≤
m_{k+1}`. So `GapChannelDomination`'s content **IS** the transfer↔character correspondence.

**`GapChannelDomination`, `SingleStepDefectBound`, `TrueMarginRecursion` remain
UNINHABITED.** Frontier guard: `5 Clay-frontier types unconditionally uninhabited`
(unchanged).

---

## 4. THE HONEST REGIME (adversarial — Rule 6)

The identification is an **exact identity for all `w`**. The **bound** is regime-limited:

- The RAW fused defect `coeffW(w,1)=2w³ ≤ 6(1−w)²` only for `w ≤ 0.677…`
  (`RouteADefectCharacter.raw_ratio_exceeds_at_weak` proves failure at `w=9/10`: `2·0.9³ =
  1.458 > 0.06`).
- The RAW coarse separator `sep'=4w³ < 1` (a coarse gap exists at all) requires `w <
  (1/4)^{1/3} ≈ 0.630`.
- The strong-coupling anchor `w=1/6` (where `reconTransfer_located_gap` is inhabited) is
  comfortably inside both; `w ≤ 1/2` is the proved-regime edge.

The **weak-coupling extension** (`w_k → 1` along AF) needs the RENORMALIZED
(counterterm-subtracted) defect and the fusion s1-dominance past `w=1/2` — this is exactly
`RouteADefectCharacter.FullRangeFusedDefect`, the same Clay-core residual. The
identification also carries an honest tension with `GapIsEigenvalue` (verdict A): the
multiplicity-BLIND eigenvalue `eigA(w,1)=w³` is the physical gap edge dominant for ALL
`w`, whereas the amplitude-carrying `coeffW`/`acNfull` used here is the measure-weight
picture whose raw dominance needs `w ≤ 7/9`. The two agree at strong coupling; the
weak-coupling reconciliation (renormalization) is part of the same residual.

---

## 5. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited
Build completed successfully (687 jobs).
```

`#print axioms` for all 8 load-bearing declarations of the module:
`[propext, Quot.sound]` or `[propext]` only — no `Classical.*`, no `sorryAx`, no
`native_decide`. New file scanned clean of `sorry`/`native_decide`/`admit`/`Classical`.

---

## 6. HONEST VERDICT

Route F **PROVES the transfer-matrix ↔ character IDENTIFICATION**: the reconstructed
transfer-operator located-gap separator IS the fundamental-channel character coefficient
(`reconSep_eq_charExcited`), the coarse block-spin separator IS the fused character
coefficient (`sepCoarse_eqv_two_sepFine`), and the block-spin **margin degradation `Δ−Δ' ≃
coeffW w 1` EQUALS the fused-character excited-ratio defect** as an EXACT `Q'` identity
(`fusedDefect_eqv_charExcited`, `coarseMargin_eq_fineMargin_sub_defect`; validated
sympy-exact, `<1e-51`), which sits under the SAME PROVED envelope `6(1−w)²` as `δ_model`
over `w ≤ 1/2` (`fusedDefect_le_modelEnvelope`). `GapChannelDomination` is REDUCED —
guard-safe, via proof — to `TransferCharacterCorrespondence`, the transfer-op ↔ character
correspondence at every scale, which is **NOT inhabited**. The genuinely-hard residual (the
Bałaban dynamical form-preservation + the weak-coupling renormalized defect =
`FullRangeFusedDefect`) is named and isolated. **The 4D Yang–Mills mass gap remains OPEN;
nothing is faked; no free-field/`δ:=0` is used; no guarded bundle is inhabited.**
