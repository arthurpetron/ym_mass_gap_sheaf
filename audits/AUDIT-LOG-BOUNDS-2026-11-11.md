# Audit — Log Sandwich Bounds over Q' (2026-11-11)

## Scope & honest label
- Module: `lean/YMGap/Continuum/LogBounds.lean` (286 lines), importing `Continuum/ClusteringImpliesGapPoly.lean` (unchanged).
- Label: **infrastructure, not gap evidence; U(1)-true.** No real logarithm is defined. Every `L`-statement is for an arbitrary `L : Q' → Q'` satisfying the sandwich; the true `−log` satisfies it classically, but that is not formalized. No chart-closure claims; no frontier bundle touched.

## Proved
- `LogSandwich L`: `∀ 0 < ρ ≤ 1, 1 − ρ ≤ L ρ ∧ ρ·L ρ ≤ 1 − ρ` (division-free `L ρ ≤ (1−ρ)/ρ`). Pointwise in `ρ`, so `L` needs no `eqv`-congruence. `LogSandwich.nonneg`.
- `logSeries x N = Σ_{j=1}^N x^j/j`. With `x = 1 − ρ`: `lowerLog N ρ = S_{N+1}(x)` and `upperLog N ρ = S_{N+1}(x) + x^{N+2}/((N+2)ρ)` (`1/ρ` via `invPos`, `mul_invPos`).
  - `logSeries_ge`: `x ≤ S_{N+1}(x)`.
  - `logSeries_rem` (key invariant): `ρ + x ≃ 1`, `x ≥ 0` ⟹ `ρ·S_{N+1}(x) + x^{N+2}/(N+1) ≤ x`.
  - `lowerLog_sandwich`, `upperLog_sandwich` (both inhabit the interface, axiom-free), `lowerLog_le_upperLog`.
- `mass_le_log`: `m′·a ≤ 1 − ρ` ⟹ `m′·a ≤ L ρ`. `log_le_mass`: `1 − ρ ≤ M·a`, `ρ₀ ≤ ρ` ⟹ `ρ₀·L ρ ≤ M·a`.
- `rhoToy_log_le`: `LogSandwich L`, `0 < a ≤ 1/2`, `a ≤ ε·(3/4)` ⟹ `L(1 − a²) ≤ ε·a`. The modulus is `a₀(ε) = min(1/2, 3ε/4)`. `rhoToy_log_ge`: `a·a ≤ L(1 − a²)`. Together these close the `−log ρ/a → 0` caveat of `ClusteringImpliesGapPoly` for every sandwiched `L`.

## Not proved
- That `lowerLog ≤ −log ρ ≤ upperLog` for the real logarithm. There is no real log here; classically it follows from the series and its geometric tail.
- No link to the CReal `logRat` in `Constructive/CRealLog.lean`.

## Verification
- Mac worktree, single-file `safe_lean_build.py --jobs 1 --check-worker-limit-gib 8 --check` under `LEAN_NUM_THREADS=2 nice -n 10` (guard3): 0 errors, 0 warnings. The `ClusteringImpliesGapPoly` olean was built single-target (`+…:olean`, 8 GiB cap), with no other rebuilds.
- Axioms (temp-file `#print axioms`, file deleted): every declaration `⊆ {propext}`. No `sorry`/`Classical`/`native_decide`/`omega`/`simpa`.
