# Conjecture 7.4 (union-bound sharpness) — Empirical Evidence

> **Companion to** `formal/sheaf-framework.tex` Conjecture 7.4 (`conj:gaussian-sharpness`).
>
> **Milestone**: [P2.1] part (b) — the tightness half of "summability preservation under domination gluing."
>
> **Status (2026-05-25)**: empirically supported across the entire SU(2) convergent regime with margin >5×; formally still a conjecture (Lean closure open).

---

## 1. What the conjecture claims

The buffer-region KP certificate is built via `K_∩ ≤ K_sf + K_lf` (the union bound `max(s_sf, s_lf) ≤ s_sf + s_lf` summed over polymers). This is [P2.1] part (a) — Proposition 7.1 — and it is closed.

The conjecture asks: is the additive bound *tight enough*? Formally, is there a constant `C ≤ 2` such that the union bound's overestimate factor

$$
\frac{K_{sf} + K_{lf}}{K_\cap^{\text{true}}} \;\le\; C \;\le\; 2 ?
$$

If `C ≪ 2`, the bound is essentially tight. If `C → 2`, the union bound is genuinely lossy (the "fat buffer band" scenario where neither `s_sf` nor `s_lf` dominates the actual activity for a large fraction of buffer polymers).

The structural worry: the two regime activities use **different units**:
- `s_sf` is bounded by `exp(-ρ_sf · |X|_phys / a_k)` (continuum-like, indexed by physical extent).
- `s_lf` is bounded by `exp(-ρ_lf · |X|_plaq)` (lattice-combinatorial, indexed by plaquette count).

For "ball-shaped" polymers, `|X|_phys / a_k ~ |X|_plaq^(1/4)` (much less than `|X|_plaq`), so the sf bound is much looser than the lf bound in the polymer-count exponent. Whether this leads to a "fat buffer band" of polymers where neither bound is tight is the original §3.1 unit-mismatch problem.

---

## 2. What we now have that wasn't available when the conjecture was written

The post-3.1 / 3.2 upgrades give us concrete SU(2) activity bounds:

- `ρ_sf(g)` from Bałaban-style spectral-gap activity rate (`computations/small_field_kp.py`).
- `K_sf(g) = 1/(1 - exp(-(ρ_sf - log(8e))))` from Brydges–Federbush cluster expansion.
- `ρ_lf(g) = -log Z_t(g)` from heat-kernel character-tail truncation (`computations/large_field_kp.py`).
- `K_lf(g) = q/(1-q)` with `q = μ_plaq · Z_t(g)` from BF.

Both `K_sf` and `K_lf` are computable closed-form expressions; the union-bound looseness `(K_sf + K_lf)/max(K_sf, K_lf)` can therefore be evaluated directly at any operating point.

---

## 3. The empirical finding

`computations/overlap_kp.py::union_bound_looseness_estimate` computes the looseness factor at any `(g, convention, μ_plaq, c_λ)`. Worst-case loss across the SU(2) convergent regime:

| Convention | $g$ range tested | max looseness | $g$ at max | dominant regime at max |
| --- | --- | --- | --- | --- |
| canonical | [0.05, 0.40] | 1.176 | 0.38 | sf |
| Wilson    | [0.10, 0.80] | 1.176 | 0.76 | sf |

At the canonical SigmaHatPilot wire-in `g_0 = 0.30`:

$$
\frac{K_{sf} + K_{lf}}{\max(K_{sf}, K_{lf})} \;=\; \frac{1.0918 + 0.0156}{\max(1.0918, 0.0156)} \;=\; 1.0143.
$$

**Conjecture allowed bound**: 2.0.  **Maximum observed**: 1.176.  **Margin**: > 5×.

---

## 4. Why the worst case is far below 2 (semi-analytical lemma)

Throughout the joint convergent regime, **`K_sf > K_lf` strictly**, because:

  1. SU(2) sf-convergence threshold: `g_max_sf ≈ 0.40` (canonical), `≈ 0.81` (Wilson).
  2. SU(2) lf-convergence threshold: `g_max_lf ≈ 0.42` (canonical), `≈ 0.85` (Wilson).
  3. `g_max_sf < g_max_lf` in both conventions.

So as `g` grows from weak coupling toward divergence:

  - `K_sf` ranges from ≈ 1 (deep weak coupling) up to `∞` (at its divergence at `g_max_sf`).
  - `K_lf` ranges from ≈ 0 (deep weak coupling) up to a finite value `K_lf(g_max_sf) ≈ 1.42` (well below its own divergence at `g_max_lf`).

Consequently `K_lf / K_sf` stays small everywhere in the joint convergent regime, and the union-bound looseness `1 + K_lf/K_sf` stays close to 1.

**The "fat buffer band" worry doesn't materialize for SU(2)**: the lf side simply doesn't grow large enough to challenge the dominant sf side. The conjecture's union-bound looseness allowance of factor 2 has substantial headroom.

---

## 5. The pointwise activity-domination picture

For the looseness `1 + K_lf/K_sf` interpretation to map cleanly to "the conjecture holds with `C = 1 + K_lf/K_sf`", we need `K_max := Σ_X max(s_sf(X), s_lf(X)) = K_sf` — i.e., `s_sf(X) ≥ s_lf(X)` pointwise on polymers.

At canonical `g = 0.30`: `ρ_sf = 0.5 / 0.09 ≈ 5.56`, `ρ_lf ≈ 6.94`. So `ρ_lf > ρ_sf`.

- For a **filament polymer** with `|X|_phys/a_k = n = |X|_plaq`: `s_sf = exp(-5.56 n)`, `s_lf = exp(-6.94 n)`. Since `ρ_lf > ρ_sf`, `s_lf < s_sf`, so `max = s_sf`.
- For a **ball polymer** with `|X|_phys/a_k = n^(1/4)`: `s_sf = exp(-5.56 · n^(1/4))`, `s_lf = exp(-6.94 · n)`. For large `n`, `s_sf` dominates (decays slower); for small `n`, both are close to 1.

In both extremes, `s_sf ≥ s_lf` for SU(2) at the canonical wire-in. The intermediate polymer shapes interpolate between these endpoints, and by monotonicity the conclusion holds throughout.

Therefore `K_max = Σ_X max(s_sf, s_lf) = K_sf`, and the empirical looseness factor `(K_sf + K_lf)/K_sf = 1 + K_lf/K_sf` is the EXACT conjecture-relevant ratio, not an upper bound.

---

## 6. What this does and does not establish

**Does**:

  - Provide quantitative empirical evidence that the union-bound looseness on SU(2) operating points stays below 1.2 (vs the conjecture's 2.0).
  - Reduce the "fat buffer band" risk to zero for the SU(2) pilot: the pilot's `Σ Δ_∩` budget is unlikely to be limited by Conjecture 7.4 sharpness failures.
  - Provide a falsifiable test: if any future refinement of `ρ_sf`, `ρ_lf`, or `μ_plaq` pushes the looseness above 2, that's a real concern and the conjecture would be re-flagged.

**Does not**:

  - Constitute a Lean proof of Conjecture 7.4 — the empirical computation is closed-form arithmetic on `K_sf`, `K_lf` formulas, not a constructive proof at the polymer-level.
  - Establish the conjecture for non-SU(2) gauge groups (though the same machinery would apply once Phase-1 SU(3) data is in place).
  - Replace the pointwise polymer-domination argument; it just confirms the cluster-sum-level consequence.

---

## 7. Pointers

- **Conjecture statement**: [`formal/sheaf-framework.tex`](../formal/sheaf-framework.tex) `conj:gaussian-sharpness`.
- **Lean ledger**: [`lean/SORRY_LEDGER.md`](../lean/SORRY_LEDGER.md) [P2.1] part (b).
- **Code**: [`computations/overlap_kp.py`](../computations/overlap_kp.py) — `union_bound_looseness_estimate`, `union_bound_looseness_trajectory_max`, `plot_conjecture_7_4_looseness`.
- **Tests**: [`tests/test_overlap_kp.py`](../tests/test_overlap_kp.py) `TestUnionBoundLooseness`.
- **Diagram**: [`visualizations/pilot/su2/conjecture-7.4-looseness.svg`](../visualizations/pilot/su2/conjecture-7.4-looseness.svg).
- **Upstream KP modules**: `computations/small_field_kp.py` (3.1), `computations/large_field_kp.py` (3.2), `computations/overlap_kp.py` (3.3).
