# Audit — Clustering ⇒ Gap, Polynomial Prefactor + Family Form (2026-11-11)

## Scope & honest label
- Module: `lean/YMGap/Continuum/ClusteringImpliesGapPoly.lean` (331 lines), importing and reusing `Continuum/ClusteringImpliesGap.lean` (unchanged).
- Label: **infrastructure, not gap evidence; U(1)-true.** Abstract finite `SpectralModel` level only. No chart-closure claims; no frontier bundle touched.

## Proved
- `polyEnvelope` (Σ-style witness structure `PolyEnvelope`): explicit `A, B > 0` with `A·(n+1)^p·μ^n ≤ B·(μ+d)^n`, by recursion on `p` (halving the rate excess; division-free Bernoulli step `linear_envelope`, `envelope_step`).
- `clustering_poly_implies_coupled_le`: `∀ n, corr S n ≤ C·((n+1)^p·μ^n)` with `C, μ > 0` ⟹ every coupled live mode has `λᵢ ≤ μ`.
- `family_clustering_implies_gapBound`: observables sharing `k`/`lam` with `S`, a common rate `μ`, a cover of the live modes given as data, plus `hdead` ⟹ `SpectralGapBound S μ`. Corollary `family_clustering_implies_located` (`μ < 1` ⟹ `LocatedSpectralGap S`, `sep = μ`).
- Negative control (a) `missObs_counterexample`: an observable coupled only to the fast mode `1/2` clusters at `1/2` and satisfies `hdead`, but `¬ SpectralGapBound missObs (1/2)` (slow mode `9/10`). The cover hypothesis is necessary.
- Negative control (b) `ρ(a) = 1 − a²`: `rhoToy_add_sq` (`a² + ρ(a) ≃ 1`), `rhoToy_lattice_gap_pos` (`a² > 0`), `rhoToy_gap_per_spacing_le` (`1 ≤ ε·a + ρ(a)` for `0 ≤ a ≤ ε`, i.e. `(1−ρ)/a ≤ ε`, modulus `a₀(ε)=ε`).

## Not proved / OPEN
- The logarithmic form `−log ρ(a)/a → 0` is NOT formalized; only the `(1−ρ)/a` surrogate is (the bridge `−log ρ ≤ (1−ρ)/ρ` is not proved here).
- Connecting `corr` to genuine Wilson correlators and producing a covering observable family for 4D Yang–Mills remain open.

## Verification
- Mac worktree, `LEAN_NUM_THREADS=2 nice -n 10 safe_lean_build.py --jobs 1 --check-worker-limit-gib 8 --check` (single file, deps cached): 0 errors, 0 warnings.
- Axioms (temp-file `#print axioms`, file deleted): main theorems `{propext, Quot.sound}`; helpers `⊆` that set. No `sorry`/`Classical`/`native_decide`/`omega`/`simpa`.
