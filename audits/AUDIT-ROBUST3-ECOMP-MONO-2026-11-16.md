# Audit: Robust3EcompMono (2026-11-16)

File: `lean/YMGap/RG/Robust3EcompMono.lean` (152 lines, new). Check: direct `lean -M 6144`, 1.0 s wall, 0.9 s user CPU,
peak RSS 1702 MiB, min MemAvailable 13032 MiB, rc 0, zero warnings.

## PROVED (structural, all k)
- `ecomp_def` :27: `ecomp k = Dnq k · Bnq k` (rfl). `D_eqv` :38 splits D into its five summands.
- `D_mono` :86: D_k ≤ D_{k+1}, via the linear lemma `core` :58 with the steps
  - +1 (`A_succ` :78),
  - T1 ≤ T1' + 1/100,
  - T2 ≤ 31/100 (with T2' ≥ 0),
  - Z ≤ 4/17 + Z'.
- `B_mono` :123: B_k ≤ B_{k+1}, from L_n ↑ (`LQ_mono`), P_n ↓ (`VQ_anti`) and `div_mono` :99.
- **`ecomp_mono` :136:** `ecomp k ≤ ecomp (k+1)` for every k.
- **`r3E_eq` :144:** `r3E k = ecomp k` (equality in Q') for every k. The running max (and, by `r3Raw_eq`, the
  (k+1)/4 floor) never activates.

## Axioms
`#print axioms` was run in a temp file, since deleted. D_mono, B_mono, ecomp_mono and r3E_eq ⊆ [propext, Quot.sound].
Axiom-check process: 0.8 s, peak RSS 1662 MiB.

## Not weakened, with one remark
Monotonicity is non-strict (≤). The strict version, E_{k+1} > E_k (task2h (E)), follows from the same margin but is
not stated. The existing statements (`r3E_mono`, `r3Floor_le`, etc.) are untouched.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is direct lean against copied oleans, not lake-verified (stale-trace caveat). No chart closure is claimed.

U(1) note: these are statements about the exact rational schedule only, with no gauge-group content. The standing U(1) note (seed witness abelian-valid; a uniform gap at w ≳ 1/8 would be genuine non-abelian content) is unchanged.
