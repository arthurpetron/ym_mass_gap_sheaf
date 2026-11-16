# Audit: Robust3EcompMonoBounds (2026-11-16)

File: `lean/YMGap/RG/Robust3EcompMonoBounds.lean` (323 lines, new). Check: direct `lean -M 6144`, 1.2 s wall, 1.6 s user CPU,
peak RSS 1735 MiB, min MemAvailable 13022 MiB, rc 0, zero warnings.

## PROVED (structural, all k; m = k+4, n = k+14)
- `kappa_step` :109: κ'_n ≤ κ'_{n+1} + 2^{-(k+15)}, from `L_{n+1} = L_n + 1/((n+1)2^{n+1})` (`L_raw` :64), L ≥ 1/2, and
  the Nat core `kappa_nat` :77.
- `T1_step` :160: κ'_n·H_{m+3} ≤ κ'_{n+1}·H_{m+4} + 1/100. Uses H_m ≤ m (`harm_le` :41) and 100(k+7) ≤ 2^{k+15}
  (`pow_bound` :138).
- `T2_le` :254: κ'_n²(H_m+1)/m ≤ 31/100. Uses κ'_n ≤ 62/100 (`kQ_le` :172, from L_n ≥ L_14 ≥ 69/100, `L_069` :59) and
  H_m + 1 ≤ 4m/5 (`harm45` :187, `harm1_le` :210).
- `seg_shift` :278: seg(m, r+1) ≃ 1/m + seg(m+1, r). `Z_step` :305: (16/17)seg(m,17) ≤ 4/17 + (16/17)seg(m+1,17).
- Axioms (temp file, deleted): kappa_step, T1_step, T2_le, seg_shift, Z_step ⊆ [propext, Quot.sound]. There is no
  sorry, admit, Classical, native_decide, omega, simpa or grind.

The bounds are deliberately crude (e.g. dropping T2 entirely). Their sum, 1/100 + 31/100 + 4/17 ≈ 0.555 < 1, is all
that `Robust3EcompMono` needs.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is direct lean against copied oleans, not lake-verified (stale-trace caveat). No chart closure is claimed.

U(1) note: these are statements about the exact rational schedule only, with no gauge-group content. The standing U(1) note (seed witness abelian-valid; a uniform gap at w ≳ 1/8 would be genuine non-abelian content) is unchanged.
