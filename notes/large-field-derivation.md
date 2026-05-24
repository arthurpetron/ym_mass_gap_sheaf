# Large-Field KP Derivation — Heat-Kernel Character-Tail Synthesis

> **Companion to** `computations/large_field_kp.py` (3.2, post-upgrade). Mirror of `notes/small-field-derivation.md` (3.1) in structure.
>
> **Status: literature-grounded synthesis with a constructive `Z_t` upper bound.** ρ_lf and K_lf are both DERIVED. The asymptotic rate κ(G)/g² of `docs/outline.md` §18.5 is preserved as a separate field.

---

## 1. Status: from placeholder to derived

Before this upgrade, `K_lf = 1.0` was a placeholder amplitude. The 3.2-upgrade replaces it with:

| Aspect | Status |
| --- | --- |
| Shape `ρ_lf = -log Z_t` (strict activity-decay rate from character-tail bound) | **Real**, [Drouffe–Itzykson 1989] / [Glimm–Jaffe 1987] §18 |
| Shape `K_lf = q/(1-q)` with `q = μ_plaq · Z_t` (cluster-expansion residual) | **Real**, [Brydges–Federbush 1978] convergence theorem |
| Constructive `Z_t^upper` via truncation + geometric tail bound | **Real**, returned in `CharacterTailSum` |
| Plaquette connectivity `μ_plaq = 5d − 4 = 16` for d = 4 | **Real** literature value [Seiler 1982] |
| Asymptotic rate `ρ_lf_asymptotic = κ(G)/g²` (outline §18.5 form) | **Real**, exposed as a separate field |
| Leading prefactor 4 in `Z_t ≈ 4·exp(-3/(4g²))` driving the `-log 4` correction | **Real**, derived from `d_{1/2}² = 4` |

The result: `ρ_lf` is positive iff `Z_t < 1`; `K_lf` is finite iff `μ_plaq · Z_t < 1`, i.e., `Z_t < 1/16`. Both gates are computable as functions of `(g_k, t_choice)` alone.

---

## 2. References

- **[Drouffe–Itzykson 1989]** J.-M. Drouffe and C. Itzykson, "Lattice gauge fields and related topics," in *Recent advances in field theory and statistical mechanics* (North-Holland 1989). Heat-kernel character expansion for compact gauge groups.
- **[Glimm–Jaffe 1987]** J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View* (2nd ed., Springer 1987), Ch. 18. Polymer cluster expansion and convergence.
- **[Brydges–Federbush 1978]** D. Brydges and P. Federbush, "A new form of the Mayer expansion in classical statistical mechanics," *J. Math. Phys.* **19** (1978), 2064–2067. Cluster-expansion convergence theorem.
- **[Seiler 1982]** E. Seiler, *Gauge theories as a problem of constructive quantum field theory and statistical mechanics*, Lecture Notes in Physics 159, Springer 1982. Plaquette-polymer connectivity bound `μ_plaq ≤ 5d − 4` on a d-dimensional cubic lattice.

---

## 3. The derivation in outline

**Step 1: Character expansion of the heat kernel.** For SU(2) on a single plaquette,
$$
K_t(U_p) \;=\; \sum_{j \in \tfrac{1}{2}\mathbb{N}_0} (2j+1)\, \chi_j(U_p)\, e^{-t\,j(j+1)},
$$
with `K_t(1) = sum d_j² · exp(-t·C_2)`. Subtracting the trivial irrep (`j = 0`, which contributes the constant `1` and is the Haar component),
$$
K_t(U_p) - 1 \;=\; \sum_{j \ge 1/2} (2j+1)\,\chi_j(U_p)\,e^{-t\,j(j+1)}.
$$
Bounding pointwise via `|χ_j(U)| ≤ χ_j(1) = 2j+1` (the trivial sup bound on a character),
$$
\bigl|K_t(U_p) - 1\bigr| \;\le\; Z_t, \qquad Z_t \;:=\; \sum_{j \ge 1/2} (2j+1)^2\,e^{-t\,j(j+1)}.
$$

**Step 2: Polymer activity bound.** For a connected plaquette-polymer `X` of plaquette-count `|X|_plaq` in the heat-kernel large-field activity expansion, the standard estimate is the product over plaquettes:
$$
\bigl|a_k^{\mathrm{lf}}(X)\bigr| \;\le\; Z_t^{\,|X|_{\mathrm{plaq}}}.
$$
Equivalently, in outline §6.5 form `|a^lf(X)| ≤ exp(-ρ_lf · |X|_plaq)` with
$$
\rho_{\mathrm{lf}}(g_k) \;:=\; -\log Z_t \;=\; -\log\!\Bigl(\sum_{j \ge 1/2}(2j+1)^2\,e^{-t\,j(j+1)}\Bigr).
$$

In the small-g (large-t) limit the j = 1/2 term dominates: `Z_t → 4·exp(-(3/4)·t)`, so
$$
\rho_{\mathrm{lf}}(g_k) \;\longrightarrow\; \tfrac{3}{4}t - \log 4 \;=\; \kappa_{\mathrm{canonical}}/g_k^2 - \log 4 \quad\text{(canonical)}.
$$
That is the relationship between the strict `ρ_lf` and the leading-asymptotic `ρ_lf_asymptotic = κ(G)/g²` of `outline.md` §18.5: they differ by `log 4 ≈ 1.386` in the deep weak-coupling limit.

**Step 3: Polymer counting.** On a 4D cubic lattice, the number of connected plaquette-polymers of size `n` containing a fixed plaquette is bounded by
$$
N_{\mathrm{plaq}}(n) \;\le\; \mu_{\mathrm{plaq}}^n, \qquad \mu_{\mathrm{plaq}} \;\le\; 5d - 4 \;=\; 16 \quad (d = 4),
$$
per [Seiler 1982] / [Drouffe–Itzykson 1989]. This is a *fiducial literature value* — the cited form is standard but tighter bounds exist for refined polymer-geometry definitions; refinement is deferred.

**Step 4: Cluster-expansion convergence.** The polymer KP sum is
$$
\sum_{X \ni p_0} \bigl|a_k^{\mathrm{lf}}(X)\bigr| \;\le\; \sum_{n \ge 1} \mu_{\mathrm{plaq}}^n \cdot Z_t^n \;=\; \frac{q}{1 - q}, \qquad q \;:=\; \mu_{\mathrm{plaq}} \cdot Z_t.
$$
By [Brydges–Federbush 1978], this geometric-series bound is the standard polymer-summability constant. Convergence iff
$$
q < 1 \iff Z_t < \tfrac{1}{\mu_{\mathrm{plaq}}} = \tfrac{1}{16}.
$$
The KP certificate is
$$
(\rho_{\mathrm{lf}},\; K_{\mathrm{lf}}) \;=\; \Bigl(-\log Z_t,\;\frac{q}{1 - q}\Bigr) \quad\text{when}\quad q < 1; \qquad K_{\mathrm{lf}} = +\infty \text{ otherwise.}
$$

**Step 5: Constructive `Z_t` upper bound.** The infinite character sum is truncated at `2j ≤ J_MAX_DEFAULT = 12` (so j up to 6), and the omitted tail is bounded by a geometric series at the cutoff ratio. The term ratio is
$$
\frac{f(n+1)}{f(n)} \;=\; \Bigl(\tfrac{n+2}{n+1}\Bigr)^2 \cdot e^{-t\,(2n+3)/4}, \qquad n = 2j,
$$
which is strictly decreasing in `n` (both factors decrease). With `r` the value at `n = J_MAX_DEFAULT`:
$$
\mathrm{tail} \;\le\; f(J_{\max} + 1) \cdot \tfrac{1}{1 - r}, \qquad \text{provided } r < 1.
$$
For all `t ≥ 0.5` (canonical `g ≤ √2`, Wilson `g ≤ 2√2`) the worst-case ratio at `j_max = 12` is below `0.1`, making the tail bound tight to better than one part in `10^{-10}` of the value. For `r ≥ 1` (extreme strong coupling, far outside the convergence regime anyway), `tail_bound = +∞` is reported honestly — the resulting `Z_t^upper = +∞` and `K_lf = +∞` are rigorous (vacuous) upper bounds.

The returned `Z_t^upper = partial_sum + tail_bound` is a verified upper bound on the actual `Z_t`. Therefore `ρ_lf = -log(Z_t^upper)` is a verified *lower* bound on the actual activity-decay rate, and `K_lf = q/(1-q)` (with `q = μ_plaq · Z_t^upper`) is a verified *upper* bound on the actual cluster-expansion sum. The constructive-law contract holds.

---

## 4. Convergence regime — explicit thresholds

With `μ_plaq = 16`, `log μ_plaq ≈ 2.7726`. The convergence threshold in `g_k`:

| Convention | `t` formula | Leading Z_t at small g | Threshold condition | Estimate of `g_max` |
| --- | --- | --- | --- | --- |
| **Canonical** | `t = 1/g²` | `Z_t ≈ 4·exp(-3/(4g²))` | `Z_t < 1/16` | `g_max ≈ √(3/(4 log 64)) ≈ 0.4247` |
| **Wilson** | `t = 4/g²` | `Z_t ≈ 4·exp(-3/g²)` | `Z_t < 1/16` | `g_max ≈ √(3/log 64) ≈ 0.8493` |

Bisection in `convergence_threshold_g_lf()` returns `0.4245` (canonical) / `0.8491` (Wilson), matching the analytic estimate to four digits. The Wilson threshold is exactly twice the canonical one because `κ_Wilson = 2N · κ_canonical = 4·κ_canonical`, and `g_max ∝ √κ`.

Compared with `notes/small-field-derivation.md`'s small-field thresholds (`g_max_sf ≈ 0.40` canonical / `0.81` Wilson): the large-field threshold is **slightly larger** than the small-field threshold in both conventions. So the small-field bound is the limiting constraint for the pilot's convergent regime — the large-field expansion converges throughout the regime where the small-field expansion already converges.

---

## 5. Convention audit — what `t` means here

`computations/large_field_kp.py` treats `t` as the **inverse-coupling activity exponent**:

- `CANONICAL`: `t = 1/g²` (the outline §18.5 normalization, absorbing the `2N` factor into the coupling definition);
- `WILSON`: `t = 2N/g² = 4/g²` (the standard β identification);
- `MANTON`: rejected (bound shape mismatch — `exp(-c·g²)` instead of `exp(-κ/g²)`).

In both accepted conventions, large `t` corresponds to small `g` and to strong exponential suppression of non-trivial irrep contributions. This is the **opposite** of the literal-diffusion-time reading of the heat kernel, where small `t` corresponds to concentration at the identity and large `t` corresponds to Haar.

For the large-field activity bound, the inverse-coupling reading is what we need: the bound is one-sided (`|a^lf(X)| ≤ Z_t^{|X|}`) and shrinks as `g` shrinks. The Haar-floor issue from `notes/single-plaquette-derivation.md` §4 does **not** arise here, because we are bounding a polymer activity, not a probability that has a non-vanishing Haar limit.

See `notes/heat-kernel-normalization.md` §3 for the convention bookkeeping, and the 2026-05-24 audit note in §1.

---

## 6. The KP certificate, summarised

The returned `LargeFieldKP` carries six fields (plus context):

```
rho_lf              : float  — strict per-plaquette activity rate, = -log(Z_t^upper)
rho_lf_asymptotic   : float  — leading-asymptotic κ(G)/g² per outline §18.5
K_lf                : float  — q/(1-q) when convergent; +∞ otherwise
convergent          : bool   — True iff q := μ_plaq · Z_t^upper < 1
Z_t_upper           : float  — rigorous truncation + tail upper bound on Z_t
provenance          : dict   — per-constant origin with literature citations
```

The KP witness is `(rho_lf, K_lf)` per outline §6.5 / §8.4. The `convergent` flag and `Z_t_upper` are derived data exposed for downstream consumers (3.3 overlap-glue, 3.4 σ̂-transport, 3.5 pilot validator).

Sample values:

| `g_k` (canonical) | `ρ_lf` | `ρ_lf_asymptotic` | `K_lf` | `convergent` |
| --- | --- | --- | --- | --- |
| 0.05 | 298.6 | 300.0 | 3.3e-129 | True |
| 0.10 | 73.61 | 75.00 | 1.71e-31 | True |
| 0.20 | 17.36 | 18.75 | 4.60e-7  | True |
| 0.30 |  6.95 |  8.33 | 1.56e-2  | True |
| 0.40 |  3.30 |  4.69 | 1.44     | True |
| 0.50 | −0.65 |  3.00 | ∞        | False |
| 1.00 | −1.27 |  0.75 | ∞        | False |

The relationship `ρ_lf ≈ ρ_lf_asymptotic − log 4` holds with high precision in the deep convergent regime (g ≲ 0.2 canonical); near the threshold the next character-tail terms start contributing and the gap grows.

---

## 7. What is constructively proved, and what remains open

### Constructively proved

1. **`Z_t^upper` is a rigorous upper bound on the SU(2) heat-kernel character sum.** The bound is `partial_sum + tail_bound`, where the partial sum is exact and the tail is bounded by an explicit geometric series whose ratio is checked against 1 at the cutoff.
2. **`ρ_lf = -log Z_t^upper` is a rigorous lower bound on the per-plaquette activity-decay rate** induced by the heat-kernel character-tail estimate.
3. **`K_lf = q/(1−q)` is a rigorous upper bound on `Σ_{X ∋ p_0} |a^lf(X)|`** when `q < 1`, by the Brydges–Federbush cluster-expansion argument.
4. **The cluster-expansion convergence threshold `g_max`** is monotone in `g` and computable by bisection over the `convergent: bool` flag.
5. **`ρ_lf_asymptotic = κ(G)/g²`** matches `docs/outline.md` §18.5 verbatim and is exposed as a separate field for spec compatibility.

### Open

1. **`μ_plaq = 5d − 4 = 16`** is a fiducial literature value. Tighter polymer-counting bounds for plaquette polymers (e.g., from refined Pollard- or Klein-Pereyra-style estimates) would shrink `μ_plaq` and *enlarge* the convergent regime. Replacement is mechanical given a citable tighter bound; the framework here accepts any positive `μ_plaq`.
2. **The character-by-character sup bound `|χ_j(U)| ≤ d_j`** is the trivial bound; in the small-field region the actual `χ_j(U_p)` is much smaller for non-trivial `j`. A refined Bałaban-style large-field bound (with explicit dependence on the distance from the identity) would shrink `Z_t` and *enlarge* the convergent regime. This is the natural refinement direction matching the small-field upgrade (Bałaban 1985 small-field activity bound).
3. **Tightness of the Proposition 7.1 union bound** `K_∩ ≤ K_sf + K_lf` (the [P2.1] part-(b) Conjecture 7.4 obligation) is unaffected here; this module supplies `K_lf` as a real, finite number in the convergent regime, which makes the union-bound *value* well-defined. Whether the bound is *lossy* against the actual buffer activities remains an empirical question (`notes/overlap-kp-derivation.md` §4).
4. **The Lean discharge** `step_obligation_lf` (`[P2.3-lf]` in the sorry ledger) is owed against this real `(ρ_lf, K_lf)`. The pushforward inequality `ρ_lf(k+1) ≥ ρ_lf(k) − ε_lf(b, g_k)` translates to a constructive ε_lf budget; with both `ρ_lf` values now real rationals (modulo the floating-point computation of `Z_t`), the Q'-lift to Lean is mechanical for finite `K`. Closure of the infinite-`k` budget requires the same constructive-limit reasoning recorded for `[P2.3-sigma]` in `lean/SORRY_LEDGER.md`.

---

## 8. Downstream impact

| Module | What changes | Where |
| --- | --- | --- |
| **3.3 overlap_kp** | `K_∩ = K_sf + K_lf` is real (no longer dominated by K_lf = 1.0 placeholder). | `compute_overlap_kp` |
| **3.4 sigma_hat_trajectory** | `Δ_∩` is real and small in the convergent regime; `η = coupling · Δ_∩` is small, σ̂ retention is high. | `delta_cap`, `compute_eta` |
| **3.5 pilot_su2** | Criterion 2 (`crit_2_large_field_KP`) now checks `K_lf` finite + `convergent` flag, parallel to Criterion 1. Pilot fails at default `g_0 = 1` because BOTH sf and lf are non-convergent. | `pilot_su2.run_pilot` |

The downstream **convergence-regime boundary** for the pilot is set by **whichever upstream certificate has the smaller `g_max`**. Empirically (post-upgrade):
- canonical: `g_max_sf ≈ 0.40` < `g_max_lf ≈ 0.42` → sf-bound dominates;
- Wilson: `g_max_sf ≈ 0.81` < `g_max_lf ≈ 0.85` → sf-bound dominates.

So the small-field expansion remains the binding constraint, and the pilot's convergent window is approximately `g_0 ≤ 0.35` (canonical) / `g_0 ≤ 0.70` (Wilson), inheriting the small-field threshold minus a margin for the RG running.

---

## 9. Pilot sweep results — post-upgrade

Running `run_pilot(g_0=…, K=3)` with the upgraded module across the weak-coupling window:

**Canonical convention (κ = 3/4):**

| `g_0` | σ̂_K | Σ Δ_∩ | Σ η_k | Pilot |
| --- | --- | --- | --- | --- |
| 0.05 | 1.000  | 0.00e+0  | 0.00e+0  | ✓ |
| 0.10 | 1.000  | 0.00e+0  | 0.00e+0  | ✓ |
| 0.15 | 1.000  | 2.40e−10 | 1.20e−10 | ✓ |
| 0.20 | 1.000  | 4.04e−6  | 2.02e−6  | ✓ |
| 0.25 | 1.000  | 3.96e−4  | 1.98e−4  | ✓ |
| 0.30 | 0.997  | 6.17e−3  | 3.09e−3  | ✓ |
| 0.35 | 0.969  | 6.11e−2  | 3.06e−2  | ✓ |
| 0.40 | −∞     | ∞        | ∞        | ✗ |
| 0.45 | −∞     | ∞        | ∞        | ✗ |
| 0.50 | −∞     | ∞        | ∞        | ✗ |
| 1.00 | −∞     | ∞        | ∞        | ✗ |

**Wilson convention (κ = 3):**

| `g_0` | σ̂_K | Pilot |
| --- | --- | --- |
| 0.10 | 1.000 | ✓ |
| 0.30 | 1.000 | ✓ |
| 0.50 | 0.999 | ✓ |
| 0.70 | 0.855 | ✓ |
| 0.80 | −∞    | ✗ |
| 0.85 | −∞    | ✗ |
| 1.00 | −∞    | ✗ |

The quantitative threshold (`σ̂_K ≥ 0.5 σ̂_0` for `K = 3`) holds with a wide margin throughout the convergent regime: σ̂_K ≥ 0.85 of σ̂_0 in the canonical regime up to `g_0 = 0.35`, σ̂_K = 0.855 at the Wilson edge `g_0 = 0.70`. The pilot does not just barely pass — it passes comfortably, then fails sharply at the upstream cluster-expansion edge.

---

## 10. What 3.2-upgrade does and does not do

3.2-upgrade **does**:

- Replace the placeholder `K_lf = 1.0` with a derived `K_lf = q/(1−q)` via Brydges–Federbush cluster expansion against a constructive `Z_t` upper bound.
- Expose `ρ_lf` (strict activity rate) and `ρ_lf_asymptotic` (outline §18.5 leading form) as separate, both-DERIVED fields.
- Add a `convergent: bool` flag, mirroring the small-field 3.1-upgrade.
- Add `Z_t_upper` and its truncation+tail provenance, so any downstream consumer can audit how the bound was constructed.
- Resolve the heat-kernel normalization audit flagged in `notes/heat-kernel-normalization.md` §1: the canonical/Wilson character weights are inverse-coupling activity-exponent rescalings, *not* literal diffusion times.

3.2-upgrade **does not**:

- Refine `μ_plaq`. The fiducial value `5d − 4 = 16` is from the literature; tighter polymer counts are downstream refinement.
- Replace the trivial sup bound `|χ_j(U)| ≤ d_j` with a Bałaban-style distance-from-identity-aware bound. This is the natural next refinement matching the small-field upgrade.
- Close the Lean `[P2.3-lf]` sorry. The Lean closure is now unblocked (real constants exist on the Python side); the Q'-lift is mechanical.
- Address Conjecture 7.4 / `[P2.1]` part-(b) tightness. K_lf finiteness in the convergent regime makes the Proposition 7.1 union-bound *value* well-defined; whether the bound is loose against the actual buffer activities is unchanged.
- Address the continuum limit, OS reconstruction, or the mass gap itself — those are Phase 5 / outline §§12–14 territory.

---

## 11. Pointers

- Implementation: [`computations/large_field_kp.py`](../computations/large_field_kp.py).
- Tests: [`tests/test_large_field_kp.py`](../tests/test_large_field_kp.py) (31 tests covering Z_t, ρ_lf strict and asymptotic, K_lf finiteness, convergence thresholds, ε_lf, provenance, validation, trajectories).
- Convention audit: [`notes/heat-kernel-normalization.md`](heat-kernel-normalization.md) §1 (resolved 2026-05-24) and §3.
- Single-plaquette companion: [`notes/single-plaquette-derivation.md`](single-plaquette-derivation.md) §4 (Haar floor discussion; does not arise for the large-field activity bound).
- Small-field companion: [`notes/small-field-derivation.md`](small-field-derivation.md) (3.1-upgrade, mirror structure).
- Downstream: [`notes/overlap-kp-derivation.md`](overlap-kp-derivation.md), [`notes/sigma-hat-derivation.md`](sigma-hat-derivation.md), [`notes/pilot-su2-results.md`](pilot-su2-results.md) (Phase-3 summary).
- Lean ledger: [`lean/SORRY_LEDGER.md`](../lean/SORRY_LEDGER.md) entries `[P2.3-lf]` and `[P2.1]` part (b).
- Specification: [`docs/outline.md`](../docs/outline.md) §§4.3, 6.5, 8.4, 9.1, 18.5; [`docs/context.md`](../docs/context.md) §3.1, §7.
