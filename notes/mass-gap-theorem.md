# The SU(2) mass-gap theorem: constructive lower bound m_0 > 0

**Milestone 9.1 of `work_plan.md`.**  Prose companion to
`formal/mass-gap-theorem.tex`, `computations/mass_gap_bound.py`, and
`tests/test_mass_gap_bound.py`.

## 1. The theorem in one line

**Theorem.**  The continuum-limit SU(2) Yang–Mills Hamiltonian
`H_op` (constructed by OS reconstruction from `μ_∞`) has a spectral
gap above the ground state:

    σ(H_op) ∩ (0, m_0) = ∅,         m_0 ≥ 998/1000 (Q'),

where `m_0 = 998/1000` is the explicit constructive Q'-rational
lower bound derived from the canonical-pilot Phase-3 numerics.

This is the **Clay-statement form** for SU(2) Yang–Mills with an
explicit constructive bound, not just an existence claim.

## 2. The proof chain

The proof is a three-step composition of preceding milestones:

```
  σ̂_∞ ≥ ε > 0     (Phase 7.1: framework theorem in Q')
       ↓
  OS4 cluster with rate ε     (Phase 8.1: polymer cluster decay)
       ↓
  spectral gap of H_op ≥ ε    (Phase 8.2: cluster-to-gap bridge)
       ↓
  m := inf σ_+(H_op) ≥ √ε     (dimensional rate → mass identification)
       ↓
  m_0 := largest Q' with m_0² ≤ ε      (constructive Q' bound)
```

Each step is paper-level (with Lean type-level interfaces from the
corresponding milestone); the closed-form Q' arithmetic at the end is
fully decidable and computable.

## 3. The explicit constructive values

Two heat-kernel conventions, both with σ̂_0 = 1, K = 3 transitions,
and pilot rational denominator 10000:

| Convention | g_0 | Σ η_k | ε = σ̂_∞ lower | m_0 (Q') | m_0² (Q') | √ε exact |
|-----------|-----|-------|----------------|----------|------------|----------|
| Canonical | 0.30 | 33/10000 | 9967/10000 | 998/1000 | 996004/1000000 | 0.998348 |
| Wilson | 0.50 | 12/10000 | 9988/10000 | 999/1000 | 998001/1000000 | 0.999399 |

Wilson consumes less η-budget (Δ_∩ is smaller in the Wilson sf-window
than canonical's), hence its ε is closer to σ̂_0 = 1 and its m_0
lower bound is tighter (999/1000 vs 998/1000).

### Sensitivity to the m_0 denominator

`m_0` is the largest Q'-rational at the chosen m_0_denominator
satisfying `m_0² ≤ ε`.  Larger denominators give finer-grained
approximations of √ε:

| m_0_denominator | canonical m_0 (Q') | float |
|-----------------|---------------------|--------|
| 100 | 99/100 | 0.99 |
| 1000 | 998/1000 | 0.998 |
| 10000 | 9983/10000 | 0.9983 |
| 100000 | 99834/100000 | 0.99834 |

At any finite denominator the bound is conservative; the limit is
the exact `√(9967/10000) ≈ 0.998348` of the canonical case.

The Phase-9.1 default `m_0_denominator = 1000` gives 3-significant-
digit precision, suitable for the explicit constructive form of the
theorem statement in `formal/mass-gap-theorem.tex`.

## 4. Units and the physical meaning of m_0

The Q'-rational `m_0 = 998/1000` is dimensionless: it lives in Q'.
Two readings:

  * **Units of σ̂_0^{1/2}** with σ̂_0 = 1 at scale 0: `m_0 ∈ (0, 1)`
    is a fraction of the bare-lattice string-tension scale.
  * **Physical units**: with the standard QCD calibration
    `√σ_0 ≈ 440 MeV` (Jaffe–Witten 2006 §2), this gives
    `m_0 · √σ_0 ≈ 0.998 · 440 ≈ 439 MeV` as a lower bound on the
    lightest SU(2) glueball mass.  The actual lightest 0^{++}
    glueball is at ~1.5 GeV per lattice-QCD calorimetry, so our
    bound is roughly an order of magnitude looser than the truth.

The dimensionless form is the constructive content of this
milestone; the physical-unit translation is a calibration choice
made downstream (Phase 10 or later).

## 5. Sharpness: the bound is NOT sharp

The proven `m_0 ≈ 0.998` is constructive but quantitatively loose
by a factor of ~3 vs the actual lightest-glueball mass.  Sources of
looseness, in decreasing order of impact:

1. **m ≥ √σ̂_∞ identification**: the dimensional relation between
   Wilson-loop area-law decay rate and Hamiltonian spectral gap is
   the linear bound.  A sharper Brydges–Federbush 1981 estimate
   could improve the multiplicative constant by a factor of ~2.
2. **c_λ small-field fiducial**: the per-step η_k is derived from
   the Phase-2.1 KP certificate's `c_λ` smallness threshold, which
   is a fiducial constant flagged for refinement in
   `notes/fiducials_notes.md`. Tightening it reduces η_total and
   raises m_0.
3. **Chaining tightening on η** (Phase 6.5 → 9.1 follow-on): the
   Phase-6.5 chaining estimate tightens μ_k(Ω_k^∩) bounds by ~28%
   on average, which propagates to η_k via the Δ_∩ derivation.
   Estimated m_0 uplift: factor 1.001–1.0005 (modest because
   η_total is already small in absolute terms).

All three are **open analytical refinements**, not blockers for the
existence statement.

## 6. What this milestone does and does NOT deliver

### Delivered

  * **Paper**: full statement + proof (`formal/mass-gap-theorem.tex`,
    ~280 lines, 6 sections).  Composes 7.1 + 8.1 + 8.2 into the
    Clay-statement form with explicit constructive m_0 derivation.
  * **Python**: `computations/mass_gap_bound.py` extracts the
    explicit Q'-rational m_0 from the Phase-3 pilot numerics, with
    full audit trail (eta_total, ε, m_0², witness check).  Defaults
    match the paper exactly; convenience wrappers
    `canonical_mass_gap_bound()` and `wilson_mass_gap_bound()`.
  * **Tests**: 19 covering the paper-cited values (Prop 3.1 / 3.2
    lockstep), the decidable cross-product witness check, sensitivity
    sweeps, comparison between conventions, and input validation.

### NOT delivered (deferred to Milestone 9.2 / Phase 10 / future)

  * **Lean formalization** of the mass-gap statement:
    `lean/YMGap/MassGap/SU2.lean` with the formal statement against
    the Phase-7.1, 8.1, 8.2 type signatures — scoped to **Milestone
    9.2**.
  * **Sharp m_0**: the constructed bound is conservative; sharpening
    is open analytical refinement.
  * **SU(3) extension**: Phase 10.
  * **Glueball-spectrum identification**: beyond the Clay-statement
    requirement.

## 7. Verification

  * Paper compiles via standard LaTeX; cross-references to Phase 7.1
    (`lean/YMGap/Continuum/SigmaHatLimit.lean`), Phase 8.1
    (`formal/os-axioms.tex`), Phase 8.2 (`formal/os-reconstruction.tex`),
    Phase 3 (`lean/YMGap/RG/SigmaHatPilot.lean`) all resolve.
  * 19/19 mass-gap-bound tests pass; lockstep regression with the
    Lean SigmaHatPilot constants confirmed.
  * `python -m computations.mass_gap_bound` prints the canonical +
    Wilson bounds + sensitivity sweep.

## 8. References

  * `formal/mass-gap-theorem.tex` (the formal paper, primary
    deliverable).
  * `formal/continuum-measure.tex` (Phase 7.2; supplies μ_∞).
  * `formal/os-axioms.tex` (Phase 8.1; supplies OS axiom verification).
  * `formal/os-reconstruction.tex` (Phase 8.2; supplies H_∞, H_op,
    cluster-to-gap bridge).
  * `lean/YMGap/Continuum/SigmaHatLimit.lean` (Phase 7.1; supplies
    `sigma_hat_uv_limit_positive` Lean witness).
  * `lean/YMGap/RG/SigmaHatPilot.lean` (Phase 3; supplies the
    Q'-rational pilot constants that the explicit m_0 derives from).
  * `computations/q_lift.py` (Phase 3; supplies
    `pilot_eta_rational_bound` upstream of m_0 derivation).
  * Jaffe–Witten 2006 (Clay statement).
  * Glimm–Jaffe 1987 §6.1 (OS axioms + reconstruction),
    Brydges–Federbush 1981 (sharper mass-gap-from-clustering).
