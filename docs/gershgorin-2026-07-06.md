# The cross-strand reserve: Gershgorin verdict for `SymMinorGershgorin` / `AutoconvReserveResidual`

**Date:** 2026-07-06 · **Node:** the single open residual the fusion-box log-concavity core
(`FusionConvLogConcaveCore`) reduces to via both Track A and Track B.
**New Lean file:** `lean/YMGap/Continuum/FusionCoreStepRoundL.lean` (imported in `YMGap.lean`).
**Build:** full `lake build` GREEN = **669 jobs** (+1). `YMGapGuard` **OK** (5 Clay-frontier
types unconditionally uninhabited). No `sorry` / `Classical.*` / `native_decide` / custom
`axiom`. Every new decl axiom-gated (`propext` / `Quot.sound` only; the 7 `decide` facts depend
on **no axioms**).

---

## 1. The exact residual and the quadratic form (extracted)

From `AutoconvGershgorin.lean` the sole open field is `SymMinorGershgorin w`:

```
∀ s,  2·(31/225)·(acN(s+1,s)·acN(s+1,s+2))  ≤  Σ_{i,j<s+1} c_i c_j · symMinor(s−i, s−j)
```

with (all from the tree, verified):

- `coeffW w s = c_s = (s+1)·w^{s(s+2)}`   (heat-kernel weight; `wH = 1/2`).
- `acN(w,n,s) = Σ_{p<n} c_p·c_{s−p}`   (range-`n` central autoconvolution).
- `symMinor(w,m,n) = 2 c_{m+1} c_{n+1} − (c_m c_{n+2} + c_n c_{m+2})`   (Round J; diagonal
  `symMinor(m,m) = 2δ_m ≥ (3/2)c_{m+1}²`, off-diagonal indefinite = `symMinor_can_be_negative`).

Via the **proved** Andréief half-sum identity `acN_defect_double_eq`
(`Σ c_i c_j symMinor = 2(B−A)`), this residual is **equivalent** to the truncated-block reserve

> **(†)**   `(1 + 31/225)·acN(s+1,s)·acN(s+1,s+2) ≤ acN(s+1,s+1)²`,   i.e. `(256/225)·A ≤ B`.

**Diagonal (proved, Round K `coeffW_strandReserve`):** the single-strand reserve holds with a
uniform ≈3.5× cushion, because super-log-concavity gives `c_s c_{s+2} ≤ (1/4)c_{s+1}²` and
`(256/225)·(1/4) = 64/225 ≤ 1`.

**The reserve as a matrix.** Symmetrizing `A` and folding the reserve into the diagonal, (†) is
exactly

> `B − (256/225)·A = Σ_{p,q≤s} c_p c_q · reserveM(w,s,p,q) ≥ 0`,
> `reserveM(w,s,p,q) = c_{s+1−p}c_{s+1−q} − (128/225)·(c_{s−p}c_{s+2−q} + c_{s−q}c_{s+2−p})`.

This identity was verified exactly (sympy, diff = 0) and its pointwise core is **proved in
Lean** (`twoReserveM_link`: `2·reserveM(s,p,q) ≃ symMinor(s−p,s−q) − δ·(c_{s−p}c_{s+2−q}+c_{s−q}c_{s+2−p})`).
`reserveM` has **positive diagonal** (the ≈3.5× cushion; `reserveM_diag_pos`) and **indefinite
off-diagonal** (`reserveM_offDiag_neg`, `reserveM(1/2,2,0,2) = −1409/29491200 < 0`).

## 2. NUMERIC verdict (mpmath dps ≥ 40, exact sympy cross-checks)

**Is (†) even true?** YES at strong coupling, NO near `w = 1`:

| regime | worst `B/A` | vs need `256/225 = 1.1378` | verdict |
|---|---|---|---|
| `w ≤ 1/2`, `s ≤ 28` | `1.991` (w=1/2, s=28) | margin **×1.75** | **TRUE, comfortable** |
| `w = 1/2` exact (sympy, s=0..12) | `≈ 2.0` | ✓ | TRUE (rationals) |
| `w = 63/64`, `s = 4` | `1.123` | **< 1.1378** | **FALSE** |
| `w = 0.99`, `s = 19` (full conv, not truncation) | `1.017` | ✗ | FALSE |

So the reserve constant `256/225` is a **genuinely strong-coupling** fact: it degrades to `→1`
as `w→1` (both truncated block AND full convolution). Any proof of (†) **must** consume
`w ≤ 1/2` (matching `coeffW_superLogConcave`); the `w`-unconstrained `∀ s` statement in
`SymMinorGershgorin` is **unprovable as written** — it is only inhabitable at the physical
strong-coupling weight.

**Does Gershgorin / diagonal-dominance close it?** NO — decisively. For the `c`-weighted
reserve matrix `N_pq = c_p·reserveM_pq·c_q` (whose full sum IS the reserve), the worst row
ratio `Σ_{q≠p}|N_pq| / N_pp` **diverges**:

| `w` | `s` | worst row-ratio `Σ_{q≠p}|N_pq|/N_pp` (need `< 1`) |
|---|---|---|
| 1/2 | 4 | `1.45 × 10⁵` |
| 1/2 | 10 | `5.23 × 10²¹` |
| 1/2 | 16 | `9.15 × 10⁴⁸` |

The **sup over `w, s` is `+∞`**. The margin is not "just missed" — it is exceeded by tens of
orders of magnitude and grows with `s`. Diagonal dominance fails at every corner row `p→0` (the
diagonal `N_pp` is the reserve of the *highest* modes `s±1`, exponentially small, while the
off-diagonal couples in *low*-mode weights `c_q`).

**Is the signed form at least a matrix-PSD fact?** NO. The reserve matrix `reserveM(w,s,·,·)`
has a **strictly negative eigenvalue at every `w`** (min-eig `≈ −7.6×10⁻⁸` at `w=1/2,s=2`,
growing to `−13.9` at `w=0.99,s=10`). By Sylvester, an explicit `2×2` principal minor is
negative — see §3. So the ≈3.5× diagonal cushion cannot dominate the signed cross-strand
coupling by **any** absolute-value/Gershgorin/PSD bound.

## 3. What is PROVED in Lean (`FusionCoreStepRoundL.lean`, all axiom-clean)

| decl | content | axioms |
|---|---|---|
| `reserveM`, `reserveM_symm` | the reserve quadratic-form matrix, symmetric | `[propext]` |
| `two_minor_identity`, `twoReserveM_link` | reserveM **is** the matrix of `S − 2δA` | `[propext(,Quot.sound)]` |
| `reserveM_diag_pos` | diagonal `reserveM(1/2,2,0,0)>0` ∧ `reserveM(1/2,2,2,2)>0` | none |
| `reserveM_offDiag_neg` | `reserveM(1/2,2,0,2) < 0` (indefinite coupling) | none |
| **`reserve_matrix_2x2_minor_neg`** | **`reserveM₀₀·reserveM₂₂ − reserveM₀₂² = −1518001/869730877440000 < 0`** → not PSD, not diag-dominant | none |
| `reserve_holds_at_half_0..3` | (†) HOLDS at `w=1/2`, `s=0..3` (physical point) | none |
| `reserve_fails_near_one` | (†) FAILS at `w=63/64`, `s=4` (strong-coupling essential) | none |

`reserve_matrix_2x2_minor_neg` is **the refutation of the coordinator's Gershgorin hypothesis**:
positive diagonal but a negative principal minor ⟹ `reserveM(1/2,2,·,·)` is not
positive-semidefinite ⟹ (contrapositive of "diagonal dominance ⟹ PSD") it is not diagonally
dominant. No Gershgorin/diagonal-dominance/matrix-PSD argument can close the reserve.

## 4. HONEST VERDICT

- **The residual is TRUE where it is needed** (`w ≤ 1/2`, verified with a ×1.75 margin; exact at
  `w=1/2`). It is **FALSE near `w=1`** — the reserve is intrinsically a strong-coupling
  (local-CLT) fact, not `w`-uniform.
- **The cross-strand is NOT closed by Gershgorin.** Diagonal-dominance fails with worst row-ratio
  `→ ∞` (grows with `s`), and — stronger — the reserve quadratic-form matrix is **not PSD**
  (negative `2×2` principal minor at the physical weight `w=1/2`, machine-checked). The ≈3.5×
  diagonal cushion is real but irrelevant: it cannot dominate the signed off-diagonal by any
  absolute-value bound.
- **The genuine open content** is therefore precisely the **weight-specific SIGNED cancellation**
  `Σ_{p,q} c_p c_q reserveM(w,s,p,q) ≥ 0` for all `s` at `w≤1/2`: the specific heat-kernel weight
  vector `c_p = (p+1)w^{p(p+2)}` avoids the matrix's negative eigendirection. This is a genuine
  **heat-kernel local-CLT** inequality (super-log-concavity of `c` propagated through the
  autoconvolution), **not** a generic linear-algebra / matrix-positivity fact.
- **Nothing is closed downstream; nothing is overclaimed.** `SymMinorGershgorin` /
  `AutoconvReserveResidual` remain NAMED-OPEN; RoundL inhabits **no** guarded Clay-frontier
  bundle (`YMGapGuard` OK). This is a structural localization + refutation of the closure route
  for one box-level log-concavity sub-fact — **not** a 4D Yang–Mills mass gap.

**True sup-ratio requested by the task:** Gershgorin worst-row-ratio `sup_{w,s} Σ_{j≠i}|M_ij|/M_ii
= +∞` (diverges in `s`; `≈5×10²¹` already at `w=1/2,s=10`). Diagonal-dominance does **not** hold;
the cancellation is genuinely signed/transcendental.
