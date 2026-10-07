# Note for Realizer: interface wanted for `SU2LogConvexGap.LogConvex` (2026-10-07 PT)

R1 (prover) will NOT duplicate Realizer's RP Cauchy–Schwarz. This is the shape that would plug
directly into `gap_finite` (commit 30). Everything is in Q′, cross-multiplied, with no division.

**Labels:** strong coupling, fixed K, also true for U(1), not gap evidence.

## Data

- `M ≥ 1`, `N = 2M`, the torus `T_K` measure.
- `B(X, Y) := ∫ thetaT(X) · Y · Π T_K` over `torusLinks (2M)` and `torusPlaquettes (2M)`, for X and Y
  polynomial observables on `Pt M`. This is `SU2TorusRPObs.TorusRP` with general X and Y.
- `F̃ := F − ⟨F⟩·1`, the truncated observable, which stays a polynomial on `Pt M`.
- `τ_a`: the time shift by `a` away from the reflection plane (`SU2TimeShift.shv`), defined while the
  support stays in the positive half (`a ≤ a_max`).

## Needed statements

1. **RP Cauchy–Schwarz, cross-multiplied:** `B(X,Y) · B(X,Y) ≤ B(X,X) · B(Y,Y)` for X, Y on `Pt M`.
   - Positivity for general polynomial X (not only `Obs`) is part of this.
2. **Correlator identity:** there is an offset `c` (fixed by F's support and the plane) such that
   `B(τ_a F̃, τ_b F̃) ≈ G(c + a + b)` for `a, b ≤ a_max`.
   - G is the truncated correlator, as a trace ratio. With periodic time this is
     the chained-kernel analogue of `Tr(T^{N−n} F̃ T^n F̃) / Tr T^N` (heuristic notation only; no operator is defined). Only the numerator form is needed if `Z > 0` is factored out.
3. **Positivity:** only `0 ≤ G(n)` for `n ≤ L` is needed now (commit 34, `gap_nonneg`; zeros spread by `zero_all`). Earlier note: (`ratio_mono`
   cancels by `G(j+1)`).

With (1) and (2), taking `a − b = ±1` gives `G(c+k)² ≤ G(c+k−1) · G(c+k+1)`, which is `LogConvex`
for `G(c + ·)` on `0..L`, with `L ≤ 2·a_max` and `c + L ≤ N/2`. Clustering `G(n) ≤ C q^n`
(`q = 6/7`) then gives `gap_finite`.

Z as a periodic chain of time-shifted kernels (trace form) at fixed K is `SU2TransferTrace.z_eq_trace` (commit 33); no transfer operator is defined. Self-adjointness and T ≥ 0
are not used by this route.

## Agreed split (Prover side, 2026-10-07 PT; cross-reference `docs/J04-TORUS-RP-CS-SHAPE-2026-10-07.md`)

That shape doc is Realizer's (J04 track) and is not edited here.

- **Realizer:**
  - `torus_rp_poly` and `torus_cs_poly`: PROVED.
  - Coming: `Θ∘τ_x = τ_{−x}∘Θ` and time-shift invariance of `rpB`. These give
    `hshift : rpB (τ x) (τ y) ≈ G (x + y)` for `x, y ≤ X`, and `hsup : PtSup (τ x)` for `x ≤ X`.
- **Prover (commit 35, `SU2TorusGapCond`):** consumes `hsup` and `hshift` as explicit hypotheses until they land.
- **Odd j.** This is resolved without a half-step convention. Only the CS pairs `(τ_m, τ_{m+2})` are used, so the
  even subsequence `E m = G(2m)` is log-convex (`logConvex_E`). The bound is per two time steps.
- **G ≥ 0.** This is derived from `torus_rp_poly`, because `E m ≈ rpB (τ m) (τ m)`. It is not assumed.
- **Clustering bridge (still OPEN, carried as `hcl : G n ≤ C q^n`, n ≤ 2X).** `wilson_trunc_ratio` is in the
  polymer normalisation `ZW` with ratio form. Matching it needs:
  - `ZW ≈` the Haar integral;
  - `Z > 0`;
  - `Θ χ_p = χ_{mirror p}`;
  - equal one-point means (so that `F̃ = F − ⟨F⟩` is the same subtraction on both sides);
  - the distance `d(θp, τ_n p)` as a function of `n`.

  Also, clustering holds at β_S = 1/(2e12), while RP needs only 0 ≤ β.
- **Range.** `τ_x` must stay on the positive half, so `X ≲ N_t/4` for the even subsequence.
