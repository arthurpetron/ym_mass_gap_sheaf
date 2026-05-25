# Work Plan

This is the execution plan for the constructive Yang–Mills mass gap
program. It is organized around milestones with concrete deliverables.
The authoritative specification is `docs/outline.md`; the motivation
is `docs/context.md`; this file is the *schedule*.

Each milestone has:
- A **goal** stated as a checkable predicate.
- **Deliverables** (files that must exist for the milestone to be
  considered complete).
- **Dependencies** on prior milestones.
- **Open questions** that are expected to surface during execution but
  do not block completion.

A milestone is *closed* when all deliverables exist and at least one
external reader (which may be Claude Code in a fresh session reading
`context.md`) can reconstruct the argument from the deliverables
alone.

---

## Phase 0: Repository scaffolding

### Milestone 0.1 — Skeleton

**Goal.** The repository renders, lints, tests, and builds locally
with zero analytic content.

**Deliverables.**
- `pyproject.toml` with `numpy`, `scipy`, `sympy`, `matplotlib`,
  `pytest`, `ruff`, `mypy` as dev deps.
- `Makefile` with targets: `test`, `lint`, `figures`, `paper`,
  `clean`.
- `.gitignore` covering `_generated/`, `__pycache__`, `*.pyc`,
  `.venv`, LaTeX build artifacts.
- `README.md` with the one-paragraph project description, the
  pointer to `docs/`, and the build instructions.
- `docs/context.md`, `docs/outline.md` in place.
- One placeholder test in `tests/test_smoke.py` that passes.
- LaTeX skeleton in `formal/main.tex` that compiles to a one-page
  PDF with title and abstract only.

**Dependencies.** None.

**Open questions.** Whether to use `uv` or `pip` for environment
management. Whether to enforce 100% type coverage from the start or
ramp up.

---

## Phase 1: SU(2) representation theory pilot

### Milestone 1.1 — SU(2) irreps and Casimirs

**Goal.** Compute the SU(2) representation data needed for the
heat-kernel expansion and overlap measure bound, with explicit
numerical values and symbolic verification.

**Deliverables.**
- `computations/su2_representations.py`:
  - Enumerate irreps by half-integer spin $j \in \tfrac{1}{2} \mathbb{N}_0$ up to cutoff $j_{\max}$.
  - Return dimension $d_j = 2j + 1$ and Casimir $C_2(j) = j(j+1)$
    as `sympy` expressions and as floating-point values.
  - Verify symbolically that $C_2(1/2) = 3/4$.
  - Compute the character $\chi_j(\theta) = \sin((2j+1)\theta/2) / \sin(\theta/2)$
    on the maximal torus and verify orthogonality numerically.
- `tests/test_su2_representations.py` covering all of the above.
- `visualizations/pilot/su2/casimir-spectrum.svg` showing $C_2(j)$ for
  $j \le 5$ with the gap $C_2(\tfrac{1}{2}) = \tfrac{3}{4}$
  highlighted.

**Dependencies.** Milestone 0.1.

**Open questions.** Conventions for normalization of the
Killing form (factor-of-2 ambiguity between physics and math
conventions). The answer should be documented in
`computations/su2_representations.py` as a module-level docstring.

---

### Milestone 1.2 — Heat-kernel normalization

**Goal.** Fix and document the conversion between the heat-kernel
time parameter $t$ and the gauge coupling $g$ so that the overlap
measure bound has unambiguous constants.

**Deliverables.**
- `computations/heat_kernel.py`:
  - The Wilson-action choice $t = 2N / g^2$ for $SU(N)$.
  - The Manton-action / heat-kernel-action choice.
  - Conversion formulas with derivations in the docstring.
  - A function `kappa_from_casimir(C_2_min, t_choice)` returning the
    effective $\kappa(G)$ in the bound
    $\mu_k(\Omega_k^{\cap}) \le \cdots \exp(-\kappa(G) / g_k^2)$.
- `notes/heat-kernel-normalization.md` documenting the
  normalization choices and their effect on the SU(2) constant
  $\kappa_{SU(2)}$.
- `tests/test_heat_kernel.py` verifying numerical consistency between
  conventions.

**Dependencies.** Milestone 1.1.

**Open questions.** Whether to commit to one normalization
convention throughout the program or carry both. The
recommendation is to carry both as named constants and convert
explicitly at the boundary.

---

### Milestone 1.3 — Single-plaquette tail estimate

**Goal.** Compute the constructive bound on the single-plaquette
buffer-shell measure for SU(2) with explicit constants.

**Deliverables.**
- `computations/buffer_shell.py`:
  - Function `single_plaquette_buffer_measure(delta_k, g_k, t_choice)`
    returning a verified upper bound on
    $\Pr[\delta_k / 2 < d(U_p, 1) < 2 \delta_k]$
    under the heat-kernel measure.
  - The bound must return an explicit triple $(C, \kappa, \beta)$ so
    that the result is
    $C \cdot \exp(-\kappa / g_k^2) \cdot g_k^\beta$.
  - Each constant carries provenance: which step of the derivation
    produced it.
- `notes/single-plaquette-derivation.md` with the derivation in
  prose, cross-referenced to the code.
- `tests/test_buffer_shell.py` with sanity checks:
  - The bound is monotone in $\delta_k$.
  - The bound vanishes as $g_k \to 0$.
  - For specific test values, the bound is consistent with direct
    numerical integration of the heat kernel.
- `visualizations/pilot/su2/single-plaquette-tail.svg` showing the
  bound vs $g_k$ for several $\delta_k$.

**Dependencies.** Milestones 1.1, 1.2.

**Open questions.** Whether the bound is tight enough to survive
the union bound in Milestone 1.4. The expected answer is "not
quite" — that is what motivates the chaining argument in Phase 3.

---

### Milestone 1.4 — Union-bound overlap measure

**Goal.** Compute the full overlap measure bound for SU(2) using a
union bound over plaquettes, and explicitly check whether it beats
the polynomial factor $N_p(k) = (L_k / a_k)^4$ for realistic $g_k$.

**Deliverables.**
- `computations/overlap_measure.py`:
  - Function `union_bound_overlap(N_plaquettes, g_k, delta_k)`
    returning the SU(2) overlap measure bound.
  - Function `is_summable_in_k(g_trajectory)` that takes a sequence
    of $g_k$ from the two-loop running and returns whether the
    overlap measures are summable.
- `notes/union-bound-tightness.md` documenting:
  - Where the union bound is loose.
  - For which $(L_k / a_k)$ range it succeeds without further work.
  - The threshold $g_{\max}$ above which it fails.
- `visualizations/pilot/su2/overlap-vs-rg-step.svg` showing
  $\mu_k(\Omega_k^{\cap})$ for a realistic RG trajectory.
- `tests/test_overlap_measure.py`.

**Dependencies.** Milestone 1.3.

**Open questions.** This is the milestone most likely to surface
the need for the chaining argument in Phase 3. If the union bound
fails for realistic $g_{\max}$, document precisely where it fails
and what tightening is needed.

---

## Phase 2: Sheaf framework (formal definitions)

### Milestone 2.1 — Site and presheaf objects

**Goal.** Write down the Grothendieck site over $\Omega_k$ and the
two presheaves $\mathcal{A}_k$, $\mathcal{S}_k$ as formal
LaTeX definitions ready for the paper.

**Deliverables.**
- `formal/sheaf-framework.tex`:
  - Definition of the site (objects, morphisms, coverage).
  - Definition of $\mathcal{A}_k$ with values in $(\mathbb{R}_{\ge 0}, \le)$.
  - Proof that $\mathcal{A}_k$ is flabby.
  - Definition of $\mathcal{S}_k$ with KP data $(\rho, K)$.
  - Definition of the compatibility condition between $\mathcal{A}_k$
    and $\mathcal{S}_k$.
- `docs/sheaf-framework.md` with the informal-prose version,
  cross-referenced to the LaTeX.
- `visualizations/structure/sheaf-gluing.tikz`.

**Dependencies.** None — this is independent of Phase 1 and can run
in parallel.

**Open questions.** Whether the values of $\mathcal{A}_k$ should
be in $(\mathbb{R}_{\ge 0}, \le)$ or in the constructive reals with
explicit modulus. The recommendation is to use constructive reals
with modulus, because that is what carries the analytic content
downstream.

---

### Milestone 2.2 — Inductive state package $\mathcal{I}_k$

**Goal.** Formalize the inductive state carried across RG steps as a
named tuple and prove the type-level consistency of the inductive
step.

**Deliverables.**
- `formal/inductive-step.tex` containing the statement of the
  inductive step from `docs/context.md` §3.3 in full formal detail.
- `computations/inductive_state.py` implementing $\mathcal{I}_k$ as a
  Python dataclass with:
  - $\widehat{\sigma}_k$, $g_k$, the three KP pairs
    $(\rho_{\mathrm{sf}}, K_{\mathrm{sf}})$,
    $(\rho_{\mathrm{lf}}, K_{\mathrm{lf}})$,
    $(\rho_{\cap}, K_{\cap})$,
    and the polymer atlas $\mathcal{P}_k$.
  - A `validate()` method checking the inductive hypotheses.
  - A `step_signature()` method returning the type of the block-spin
    pushforward.
- `visualizations/structure/inductive-state.tikz`.
- `tests/test_inductive_state.py`.

**Dependencies.** Milestone 2.1.

**Open questions.** The polymer atlas $\mathcal{P}_k$ has not been
defined precisely. This milestone needs to either commit to a
definition or document the choice as still-open.

---

### Milestone 2.3 — Block-spin sheaf morphism

**Goal.** Define the block-spin map as a morphism of sites and the
induced pushforward on $\mathcal{A}_k$, $\mathcal{S}_k$.

**Deliverables.**
- `formal/block-spin-morphism.tex` with:
  - Definition of $T_b$ as a site morphism.
  - Definition of the pushforward $(T_b)_*$ on bound-witnesses.
  - Statement of the 2-cell
    $\Theta_k : (T_b)_*(\widehat{\sigma}_k) \Rightarrow \widehat{\sigma}_{k+1}$
    with degradation $\eta_k$.
- `computations/block_spin.py` with a Python representation of the
  block-spin map at the level of inductive states.
- `visualizations/structure/block-spin-2cell.tikz`.

**Dependencies.** Milestone 2.2.

**Open questions.** Whether to encode the 2-cell as a separate
typed object or as a method on `InductiveState`. The
recommendation is a separate object for clarity.

---

## Phase 3: Closing the SU(2) inductive step

### Milestone 3.1 — Small-field KP constants

**Goal.** Compute explicit $(\rho_{\mathrm{sf}}, K_{\mathrm{sf}})$
for SU(2) at scale $k$ as functions of $g_k$ and the polymer atlas.

**Deliverables.**
- `computations/small_field_kp.py`.
- `notes/small-field-derivation.md`.
- Numerical values for the first few RG steps.

**Dependencies.** Milestone 1.4, 2.2.

**Open questions.** This milestone requires either implementing
the relevant pieces of Bałaban's machinery for SU(2) or finding a
sufficient citable input. The choice affects the rest of Phase 3
substantially.

---

### Milestone 3.2 — Large-field KP constants

**Goal.** Compute explicit $(\rho_{\mathrm{lf}}, K_{\mathrm{lf}})$
for SU(2) from the heat-kernel character expansion.

**Deliverables.**
- `computations/large_field_kp.py`.
- `notes/large-field-derivation.md`.
- Numerical values for the first few RG steps.

**Dependencies.** Milestones 1.1, 1.2, 2.2.

**Open questions.** Whether the character-expansion convergence
radius is large enough at realistic $g_k$, or whether resummation
is needed.

---

### Milestone 3.3 — Overlap KP constants

**Goal.** Convert the overlap measure bound from Milestone 1.4 into
KP constants $(\rho_{\cap}, K_{\cap})$ via Hölder against polymer
activities. Verify that the block-spin pushforward gives
$\sum_k \Delta_{\cap}(b, g_k) < \infty$.

**Deliverables.**
- `computations/overlap_kp.py` with the Hölder conversion.
- `computations/delta_cap_budget.py` computing the degradation
  budget across the RG trajectory.
- `notes/overlap-kp-derivation.md`.
- `visualizations/pilot/su2/delta-cap-budget.svg`.

**Dependencies.** Milestones 1.4, 3.1, 3.2.

**Open questions.** This is the place where the Hölder exponent
choice is non-obvious. Document the choice carefully.

---

### Milestone 3.4 — String-tension 2-cell budget

**Goal.** Compute the degradation $\eta_k$ across RG steps and
verify $\sum_k \eta_k < \widehat{\sigma}_0$ for the SU(2) pilot.

**Deliverables.**
- `computations/sigma_hat_trajectory.py`.
- `visualizations/pilot/su2/sigma-hat-trajectory.svg`.
- `notes/sigma-hat-derivation.md`.

**Dependencies.** Milestones 3.1, 3.2, 3.3.

**Open questions.** This is the milestone where the pilot either
succeeds or fails. If $\sum_k \eta_k$ exceeds $\widehat{\sigma}_0$,
document where the obstruction lies and propose targeted
tightenings.

---

### Milestone 3.5 — SU(2) pilot success criterion

**Goal.** Verify all five success criteria from
`docs/context.md` §7 over a finite RG range.

**Deliverables.**
- `computations/pilot_su2.py` running the full inductive step
  validator over $k = 0, 1, \ldots, K$ for some $K \ge 3$.
- `notes/pilot-su2-results.md` documenting the outcome.
- `visualizations/pilot/su2/inductive-closure.svg` summarizing all
  five criteria.

**Dependencies.** Milestones 3.1–3.4.

**Open questions.** What "succeeds" looks like quantitatively.
Suggest: $\widehat{\sigma}_K \ge \tfrac{1}{2} \widehat{\sigma}_0$ for
$K = 3$ as a target, with the caveat that this is a calibration
check, not a Clay-level claim.

---

## Phase 4: Codynamic transfer template

### Milestone 4.1 — Explicit EKF–to–YM type-signature port

**Goal.** Write the type-signature correspondence from
`docs/context.md` §6 as a concrete code-level mapping with
runnable examples on both sides.

**Deliverables.**
- `notes/codynamic-transfer.md` with the line-by-line type mapping.
- `computations/transfer_examples/`:
  - A small EKF example using the `codynamic-sensor-data`
    inductive invariant.
  - A small YM example using the same invariant shape.
  - A test showing that the validators have isomorphic type
    signatures.
- `visualizations/transfer/ekf-to-ym-types.tikz`.

**Dependencies.** Milestone 2.2.

**Open questions.** Whether to depend on `codynamic-sensor-data`
as a Python package or to vendor the relevant invariant code.

---

## Phase 5: Paper draft

### Milestone 5.1 — Reduction theorem write-up

**Goal.** Write the paper draft establishing the *reduction*: that
the SU(2) mass gap follows from the inductive step holding with
explicit constants over the RG range computed in Milestone 3.5.

**Deliverables.**
- `formal/main.tex` with full draft.
- `formal/figures/` populated from `visualizations/`.

**Dependencies.** All Phase 1–3 milestones.

**Open questions.** Target venue. The reduction is publishable
even if the inductive step closure is conditional; the constants
calculation is publishable as a numerical experiment.

---

## Phase 6: Lean-level analytic closures and tightenings

**Phase goal.** Complete the analytic infrastructure needed to lift the
finite-K SU(2) pilot of Phase 3 to a genuine infinite-trajectory
closure with Lean-level verification, and tighten the per-plaquette
overlap-measure bound from the union estimate to a chaining estimate.
Together these close the analytical loose ends Phase 3 leaves dangling
and prepare the framework for the continuum-limit work of Phase 7.

### Milestone 6.1 — Polymer-level activity-domination lemma

**Goal.** Formal Lean closure of `[P2.1]` part (b) Conjecture 7.4:
prove at the type level that for the SU(2) heat-kernel measure, the
polymer activity domination `s_sf(X) ≥ s_lf(X)` holds for every
polymer `X` throughout the joint convergent regime, completing the
union-bound-sharpness closure that the 2026-05-25 empirical evidence
package (`notes/conjecture-7.4-empirical-evidence.md`) began.

**Deliverables.**
- `lean/YMGap/Sheaf/PolymerDomination.lean` with:
  - Theorem `polymer_dominance_sf` proving `s_sf(X) ≥ s_lf(X)` at the
    type level (filament + ball polymer extremes + interpolation).
  - Theorem `kp_sum_dominance` deriving `K_max = K_sf` from polymer-level
    domination.
  - Quantitative looseness bound `union_bound_tight_at_q_prime`
    expressing `1 + K_lf/K_sf` in Q'.
- Tests and axiom-gate `[propext]` only.
- Updated `lean/SORRY_LEDGER.md` `[P2.1]` part (b) entry: status →
  CLOSED.

**Dependencies.** `[P2.1]` part (a), Milestones 3.1, 3.2, the
2026-05-25 empirical evidence package.

**Open questions.** Whether the polymer-level domination admits a
parametric shape-class proof (filament + ball + interpolation, paralleling
the empirical argument) or requires more delicate enumeration. The
empirical evidence makes the parametric form plausible; the actual
formal proof may need an additional lemma about monotonicity of the
activity ratio across polymer shapes.

---

### Milestone 6.2 — `Q'.pow` + geometric-series sum infrastructure

**Goal.** Extend the `Q'` arithmetic with the multiplicative machinery
needed for geometric-tail derivations: `Q'.pow`, `Q'.mul` monotonicity
lemmas, and the closed-form geometric-series partial-sum bound
`Σ_{k<N} r^k ≤ 1/(1-r)` for `r : Q'` with `0 ≤ r < 1`.

**Deliverables.**
- `lean/YMGap/Constructive/Geometric.lean` with:
  - `Q'.pow : Q' → Nat → Q'` defined by structural induction.
  - Monotonicity lemmas: `Q'.mul_le_mul_of_nonneg_right`, `Q'.pow_succ`,
    `Q'.pow_le_pow_of_le`, `Q'.pow_nonneg_of_nonneg`.
  - `Q'.geometric_partial_sum_bound : ∀ N, finSum (fun k => r^k · η_max) N ≤ η_max · q_div_one_minus_r`
    for chosen `r, η_max, q_div_one_minus_r : Q'` with the divisor expressed
    as a precomputed rational (avoiding `Q'.div` as a partial operation).
- Tests and axiom-gate `[propext]` only.

**Dependencies.** Existing `Rationals.lean` and `RationalTail.lean`.

**Open questions.** Whether to expose a full `Q'.div : Q' → Q' → Q'` as a
partial operation requiring a nonzero hypothesis on the denominator, or
to restrict to the geometric-sum-shape closed form where the divisor
`1/(1-r)` is supplied externally as a rational. The latter is leaner
and sufficient for 6.4.

---

### Milestone 6.3 — UV-direction SU(2) trajectory

**Goal.** Build the asymptotic-freedom-direction SU(2) trajectory
generator (g_k → 0 as k → ∞) complementing the existing IR-direction
`standard_su2_trajectory` (which approaches the Landau pole). The UV
trajectory is the natural setting for the genuine infinite-tail closure
because η_k decays geometrically in k in this direction.

**Deliverables.**
- `computations/uv_trajectory.py` with `uv_su2_trajectory(k_max, b, g_0)`:
  - One-loop SU(2) β-function in the AF direction:
    `1/g_{k+1}² = 1/g_k² + (b_0/16π²) · log b` (note: `+`, not `−`).
  - Lattice spacing `a_{k+1} = a_k / b` (refining).
  - Per-step `η_k` exhibits geometric decay because both `K_sf` and `K_lf`
    approach 1 as g → 0.
- `tests/test_uv_trajectory.py` covering monotonicity of `g_k`, geometric
  decay of `η_k`, and the Phase-3-budget-closure check at any finite
  truncation.
- `visualizations/pilot/su2/uv-trajectory.svg`.

**Dependencies.** Phases 1.2, 3.1, 3.4, `prefix_plus_tail_closure`.

**Open questions.** Step-direction convention. Decision: in
`uv_su2_trajectory`, `k → k+1` means `a_k → a_k/b` (refining, going to UV).
The existing `standard_su2_trajectory`'s `k → k+1` means coarsening
(going to IR / Landau pole). The two trajectories flow in opposite
directions and complement each other; documentation should make this
explicit to avoid confusion.

---

### Milestone 6.4 — Genuine infinite-tail SU(2) closure

**Goal.** Compose 6.2 + 6.3 with `RationalTail.prefix_plus_tail_closure`
(already landed) for a non-zero-tail Lean-verified σ̂-budget closure on
the UV-direction SU(2) trajectory. This is the milestone where the
"infinite trajectory" terminology becomes literal in Lean — partial sums
past any finite `K_0` are bounded by a rational geometric tail derived
inside Q'.

**Deliverables.**
- `lean/YMGap/RG/SigmaHatPilotUV.lean` parallel to `SigmaHatPilot.lean`:
  - Canonical and Wilson UV-pilot rational constants from the Python
    pilot's actual UV trajectory.
  - Geometric-tail bound `∀ M, finSum η_uv (K_0 + M) ≤ S_{K_0} +
    η_max · geo_tail_bound` derived via 6.2's `Q'.geometric_partial_sum_bound`.
  - Closure: `∀ N, finSum η_uv N ≤ σ̂_0` via `prefix_plus_tail_closure`.
- `computations/q_lift.py` extension to emit the geometric decay rate
  `r ∈ Q'` and `η_max ∈ Q'` from the UV pilot data, with lockstep
  Python ↔ Lean regression tests.
- Updated `notes/sigma-hat-derivation.md` §4: infinite-trajectory closure
  is now realized for SU(2), not just framework-only.

**Dependencies.** 6.2, 6.3, `prefix_plus_tail_closure` (already in place).

**Open questions.** Choice of `r` (the geometric decay rate) for the UV
pilot — likely tied to the β-function's leading coefficient
`b_0 / (16π²)`. Sensitivity of the closure margin to `r` should be
exposed via the existing fiducial-sensitivity framework.

---

### Milestone 6.5 — Chaining-estimate tightening

**Goal.** Replace the per-plaquette union bound on `μ_k(Ω_k^∩)` in 1.4
with a chaining / correlated-plaquette estimate, per
`docs/outline.md` §17.1 and `docs/context.md` §3.4. This tightens the
aggregate buffer-measure bound below the current `Σ_k > 1` regime
that the standard trajectory exhibits, addressing the union-bound
looseness identified in 1.4's notes.

**Deliverables.**
- `computations/chaining_estimate.py` with the tightened bound.
- Comparison figure: per-step bound (chaining) vs per-step bound
  (union) across the standard trajectory.
- `notes/chaining-estimate.md` with the derivation.
- Tests covering monotonicity, dominated-bound consistency
  (chaining ≤ union), and a trajectory where chaining stays < 1 while
  union exceeds 1.

**Dependencies.** Milestones 1.3 (uniform_value), 1.4 (union bound).

**Open questions.** Whether the chaining estimate is tight enough to
admit Phase-3 budget closure at `g_0 > 0.4` (currently fails because
the small-field threshold pins the convergent regime; the union-bound
looseness is part of the issue). If the chaining estimate alone is
insufficient, the question reduces to the sf-threshold itself, which
is `c_λ`-fiducial-bound.

---

## Phase 7: Continuum limit construction

**Phase goal.** Show that the UV-direction RG flow built in Phase 6
admits a continuum limit: the renormalized string tension `σ̂_k`
converges to a positive limit `σ̂_∞ > 0`, and the lattice measures
`μ_k` admit a projective limit `μ_∞` to a continuum measure on the
continuum gauge configuration space. This is the structural precursor
to the mass-gap theorem of Phase 9.

### Milestone 7.1 — UV limit of the σ̂ trajectory

**Goal.** Prove that under the UV-direction RG flow (Phase 6.3), the
trajectory `{σ̂_k}` converges to a positive limit `σ̂_∞ > 0`, with
explicit rate (geometric or polynomial) tied to the one-loop
β-function.

**Deliverables.**
- `computations/continuum_limit.py` with `sigma_hat_uv_limit(g_0, b, ...)`
  computing the numerical `σ̂_∞`.
- Convergence theorem in `formal/continuum-limit.tex` and
  `notes/continuum-limit.md`.
- `lean/YMGap/Continuum/SigmaHatLimit.lean` with the Lean closure of
  `σ̂_uv_limit_positive : σ̂_∞ > 0` (statement at the framework level;
  the actual limit value requires a constructive-reals layer — see open
  questions).
- Tests covering convergence rate, monotonicity, and `g_0`-dependence.

**Dependencies.** Milestone 6.4 (genuine infinite-tail closure provides
the bound; the limit itself requires showing the partial sums are
Cauchy).

**Open questions.** Whether `σ̂_∞` is `g_0`-independent in the AF limit
(suggesting a universal continuum string tension) or carries residual
`g_0`-dependence. Either is publishable; the universal case is the
cleaner story for the mass-gap argument.

---

### Milestone 7.2 — Continuum measure construction

**Goal.** Define the continuum SU(2) Wilson measure `μ_∞` as a
projective limit of the lattice measures `μ_k` under the UV-direction
block-spin flow, with tightness and limit-existence proofs.

**Deliverables.**
- `formal/continuum-measure.tex` with the projective-limit construction.
- `notes/continuum-measure.md` prose companion.
- Lean type signature `continuum_measure_SU2 : ContinuumMeasure`. The
  *existence* proof likely lives at the paper level and not Lean (the
  projective-limit construction of infinite tensor products on compact
  groups is significant analytical machinery beyond the current Q' /
  constructive-reals stack).

**Dependencies.** Milestone 7.1.

**Open questions.** This is the boundary where `Q'` definitively does
not suffice and `lean/YMGap/Constructive/Reals.lean` becomes necessary
(or the formalization is paper-only). Decide explicitly at the
Milestone 7.2 kickoff whether to invest in `Constructive/Reals.lean` or
to accept a Lean-paper hybrid for the continuum limit and beyond.

---

## Phase 8: Osterwalder–Schrader reconstruction

**Phase goal.** Verify the Osterwalder–Schrader axioms for the
continuum SU(2) Wilson measure `μ_∞` (Phase 7.2) and apply the
reconstruction theorem to obtain a Hilbert space with a self-adjoint
Hamiltonian, ready for the mass-gap analysis of Phase 9.

### Milestone 8.1 — OS axiom verification

**Goal.** Verify each OS axiom (translation invariance, reflection
positivity, Euclidean / O(4) invariance after continuum limit,
exponential clustering) for `μ_∞`. Reflection positivity lifts from the
standard lattice argument via the projective limit; clustering follows
from the Phase 7.1 σ̂_∞ > 0 result.

**Deliverables.**
- `formal/os-axioms.tex` with per-axiom verification.
- `notes/os-axiom-verification.md`.
- Reflection-positivity proof using the standard lattice argument (link
  variables on each timeslice, reflection through a fixed lattice plane,
  inner-product positivity).
- Exponential-clustering proof from σ̂_∞ > 0.

**Dependencies.** Milestone 7.2, Phase 6.5 (chaining estimate
needs to be OS-compatible).

**Open questions.** Whether the chaining estimate (6.5) preserves OS
reflection positivity; if not, may need to reshape it.

---

### Milestone 8.2 — Hamiltonian reconstruction

**Goal.** Apply the OS reconstruction theorem to obtain `(H_∞, H_op)`:
a Hilbert space with a self-adjoint Hamiltonian whose spectrum will be
analyzed in Phase 9.

**Deliverables.**
- `formal/os-reconstruction.tex`: reconstruction theorem statement and
  proof, referencing 8.1 verified axioms.
- The Hilbert space `H_∞` and Hamiltonian `H_op` as defined objects
  ready for spectral analysis.
- `notes/os-reconstruction.md` prose companion.

**Dependencies.** Milestone 8.1.

**Open questions.** Lean formalization of the reconstruction is a major
undertaking (Stone's theorem, spectral theorem for self-adjoint
operators). Likely deferred to "paper-first, Lean-later" or a parallel
Lean-formal-statement-only milestone.

---

## Phase 9: Mass-gap theorem for SU(2)

**Phase goal.** State and prove the mass-gap theorem for SU(2)
Yang–Mills: the continuum-limit Hamiltonian `H_op` (Phase 8.2) has a
spectral gap above the ground state, `inf σ(H_op) \ {0} > 0`. This is
the target the entire program serves.

### Milestone 9.1 — Mass-gap statement and proof

**Goal.** State and prove the SU(2) mass-gap theorem. Proof structure:
σ̂_∞ > 0 (from Phase 7.1) → exponential clustering of Wilson loops
(from Phase 8.1) → spectral gap of `H_op` (from Phase 8.2's
reconstruction).

**Deliverables.**
- `formal/mass-gap-theorem.tex` with statement and full proof.
- `notes/mass-gap-theorem.md` companion.
- The explicit lower bound `m_0 > 0` derived from the Phase-3 pilot
  numerics — i.e. a *constructive* mass-gap statement, not just an
  existence claim.

**Dependencies.** Phases 7.1, 8.1, 8.2.

**Open questions.** Sharpness: is the constructed `m_0` the actual
gap (likely not), or just a positive lower bound? Documenting the gap
between the proven bound and the conjectured exact value is part of
the deliverable. Whether quantitative improvement of `m_0` requires
Phase-3 fiducial refinement (`c_λ` extraction, chaining tightening)
or Phase-7 / Phase-8 sharpening.

---

### Milestone 9.2 — Lean formalization of the mass-gap statement

**Goal.** Lean-formalize at least the STATEMENT of the SU(2) mass-gap
theorem and the constructive chain from σ̂_∞ > 0 through to the spectral
gap (with operator-theoretic steps potentially as type-level placeholders
or quarantined classical lemmas).

**Deliverables.**
- `lean/YMGap/MassGap/SU2.lean` with:
  - Statement: `theorem mass_gap_SU2 : ∃ m : Q', 0 < m ∧ ∀ ε ∈ Spec(H_op) \ {0}, m ≤ ε`
    (with appropriate types for `Spec` and `H_op`).
  - Path from `σ̂_∞ > 0` (Phase 7.1's Lean witness) through the OS-reconstruction
    bridge to the spectral statement.
- Updated `SORRY_LEDGER.md` reflecting which steps are formal vs paper.

**Dependencies.** Milestone 9.1 (paper-level proof), Phase 7.1 (Lean
σ̂_∞ closure), `lean/YMGap/Constructive/Reals.lean` (if built; otherwise
the spectral statement is paper-only).

---

## Phase 10: SU(N) extension framework (toward SU(3))

**Phase goal.** Identify exactly which pieces of Phases 1–9 are
SU(2)-specific and which are gauge-group-agnostic, then build the SU(3)
representation infrastructure and instantiate the inductive step for
SU(3). This converts the SU(2) mass-gap theorem into a recipe for SU(N)
extensions, with SU(3) as the immediate next target.

### Milestone 10.1 — SU(2)-specific dependency audit

**Goal.** Per-milestone audit of which Phase 1–9 deliverables use
SU(2)-specific content (Casimir values, group dimension, root system,
representation theory) vs which are abstract over the gauge group. Produce
a checklist for SU(N) extension.

**Deliverables.**
- `notes/su-N-extension-audit.md` with a per-milestone audit (Phase 1–9)
  identifying SU(2)-specific lemmas, constants, and proofs.
- An "extension recipe" specifying what changes for SU(3) vs what is
  reused.

**Dependencies.** All prior phases.

**Open questions.** Whether the abstract sheaf framework (Phase 2) was
sufficiently gauge-group-agnostic. Some leak is expected; the audit
will surface it. The SU(2)-specific places most likely to leak: P1.1
Casimir formulas, P1.2 heat-kernel conventions with `2N = 4`, P3.1's
`c_λ` fiducial (whose value may depend on N).

---

### Milestone 10.2 — SU(3) representation theory mirror

**Goal.** Mirror Phase 1.1 for SU(3): compute the Casimir spectrum,
identify the smallest non-trivial Casimir (`C_2(fund) = 4/3` for SU(3)),
verify orthogonality of characters numerically and symbolically, and
provide the SU(3)-specific spot values for downstream phases.

**Deliverables.**
- `computations/su3_representations.py` mirroring `su2_representations.py`.
- `lean/YMGap/RepTheory/SU3.lean` with the SU(3) Casimir spectrum and
  spot values at `Q'` for Lean interop.
- `tests/test_su3_representations.py` against literature values.
- `visualizations/pilot/su3/casimir-spectrum.svg`.

**Dependencies.** Milestone 1.1 (SU(2) template), 10.1 (extension audit).

**Open questions.** Convention choice for SU(3) characters (Weyl
character formula, fundamental-vs-anti-fundamental, etc.). Pick the
convention that mirrors P1.1 most cleanly.

---

### Milestone 10.3 — SU(3) inductive-step pilot

**Goal.** Instantiate the Phase-3 inductive step for SU(3) using the
10.2 representation data, verifying the framework lifts from SU(2) to
SU(3) cleanly. Identify any new analytic obstructions specific to
SU(3) (the larger group dimension affects spectral-gap thresholds and
polymer-counting constants).

**Deliverables.**
- `computations/pilot_su3.py` mirroring `pilot_su2.py`.
- `notes/pilot-su3-results.md` with the SU(3) inductive-step closure
  status (pass / fail / partial across a sweep of `g_0`).
- Updated `visualizations/pilot/su3/`.
- Updated `lean/YMGap/RG/SigmaHatPilotSU3.lean` mirroring `SigmaHatPilot.lean`.

**Dependencies.** Milestones 10.1, 10.2, all Phases 3.x (SU(2) templates).

**Open questions.** Whether the SU(3) small-field convergence threshold
is meaningfully different from SU(2)'s. The Wilson conversion factor
becomes `2N = 6` for SU(3) (vs `4` for SU(2)), which enlarges the
convergent regime in Wilson convention; in canonical convention, the
threshold depends on the spectral-gap `c_λ` which is `N`-independent at
leading order. Verifying this is part of the 10.1 audit's payoff.

---

## Cross-cutting policies

### Constructive law

Every existence claim in code must return an explicit witness. No
function may return `True` or `1` as a "proof"; it must return the
witnessing object (the bound, the modulus, the KP pair). This is
enforced by the `validate()` methods on the dataclasses.

### No law of excluded middle (LEM); no classical choice

The program is **Bishop / Martin-Löf constructive**, not merely
non-circular classical. Every theorem, lemma, and proof obligation
across the repo — Python, Lean, and LaTeX — must avoid:

- **Law of excluded middle** (`P ∨ ¬P` without exhibiting which side).
- **Proof by contradiction** for existential / data claims (`¬¬∃x. P x`
  does not constructively yield an `x`; only the direct construction does).
- **Classical choice** (selecting a witness from a nonempty set without
  a construction procedure).
- **The classical spectral theorem, Hahn–Banach, Zorn's lemma**, and
  other tools that depend on the above.

This rule binds the whole project:

- **Lean** (`lean/`): enforced by `lean/AGENTS.md` Rule 1. Every
  load-bearing theorem must pass `#print axioms foo` with no
  `Classical.choice`, no `Classical.em`, no `Classical.byContradiction`,
  no `sorryAx` in the dependency closure. `propext` and `Quot.sound`
  are allowed where they carry no erased computational content.
  Quarantined classical uses go under `YMGap/Classical/` per Rule 4 and
  are logged in `lean/CLASSICAL_LEDGER.md`.
- **Python** (`computations/`): every existence claim returns the
  witnessing data, not a bare boolean. Functions never *decide*
  existence classically (e.g. by `try/except` over a search that has no
  termination certificate); they construct the witness or report a
  bounded failure. Decidable Python branches (`if x > 0: ...`) on
  computable data are constructive; they do not invoke LEM in the
  prohibited sense.
- **LaTeX** (`formal/`): a proof presented in the paper that hides a
  non-constructive existence claim violates this rule. Each existence
  statement in the paper must point to either an explicit construction
  (with computable modulus) or a clearly-flagged constructive obligation
  owed by a downstream module.

The motivation is in `docs/context.md` §1.2 (LEM / choice usage hidden
in standard tools) and `docs/outline.md` §0.2 (the constructive law) /
§0.3 (the no-circularity law). A constructive proof of the Yang–Mills
mass gap that secretly invokes LEM is, by the standards of this
program, no proof at all.

### Test discipline

Every `computations/*.py` has a matching `tests/test_*.py`. Tests
include (a) symbolic sanity checks via `sympy`, (b) numerical
consistency across normalization conventions, (c) regression
fixtures for the SU(2) constants once stable.

### Documentation discipline

Every `computations/*.py` has a matching `notes/*.md` documenting
the derivation in prose. The Python file is the *implementation*;
the markdown is the *argument*. Both must exist for a milestone to
be closed.

### Version control discipline

Commits are small and message-prefixed by phase: `[P1.3] ...` for
Milestone 1.3 work. Branches are not required for this size of
project; the master branch should always be in a buildable state.

---

## Current status

As of 2026-05-25: Phases 0--4 are structurally closed; Phase 5
(reduction-theorem paper) is the next big-ticket item not yet started.
**Scope expanded 2026-05-25**: Phases 6--10 added to take the program
from the SU(2) pilot validator (Phase 3) through the actual SU(2)
mass-gap theorem (Phase 9), with Phase 10 setting up the SU(3)
extension that is the stated downstream goal.

The status is no longer "placeholder success"; the post-3.1 small-field
upgrade makes the default pilot fail outside the current weak-coupling
window, and post-3.4 the σ̂-budget closure is machine-verified at
finite truncation. The Phase-6+ work extends this to infinite
trajectories and continuum limits.

Closed / integrated:

- **P0.1--P2.3.** Repository scaffold, SU(2) representation data,
  heat-kernel normalization interface, buffer-shell and union-bound
  overlap code, sheaf framework, inductive state, and block-spin
  morphism are present.
- **P3.1--P3.5.** Small-field KP, large-field KP, overlap KP,
  $\widehat{\sigma}$ trajectory, and the five-criterion SU(2) pilot
  validator are wired end-to-end.
- **P3.1 post-upgrade.** `computations/small_field_kp.py` now uses a
  Bałaban/Brydges-Federbush style convergence synthesis. The
  consequence is explicit: with canonical fiducial constants,
  $g_{\max} \approx 0.40$; with Wilson constants, $g_{\max} \approx
  0.81$. Above threshold, $K_{\mathrm{sf}} = \infty$, which propagates
  to $K_{\cap}$, $\Delta_{\cap}$, $\eta$, and pilot failure.

Current pilot outcome:

- `run_pilot(g_0=1.0)` **fails** in the canonical convention because
  the small-field cluster expansion is outside its convergence window.
- `run_pilot(g_0=0.1, sigma_hat_initial=10.0)` passes the finite
  weak-coupling framework test. This is a useful sanity check, not a
  mass-gap claim.
- The local test suite passes in the repo virtualenv:
  `.venv/bin/pytest -q` gives `191 passed`.
- The Lean top-level file checks with
  `cd lean && lake env lean YMGap.lean`.

Still placeholder / open:

1. **P3.2 large-field amplitude.** $\rho_{\mathrm{lf}}$ is derived from
   the SU(2) Casimir and the chosen convention; $K_{\mathrm{lf}}$ is
   still placeholder `1.0`.
2. **P3.1 coefficient extraction.** The small-field spectral-gap
   coefficient $c_{\lambda}=1/2$ is fiducial pending direct extraction
   from the Bałaban estimates in the project's normalization.
3. **P3.4 $\eta$ coupling.** ~~Still placeholder $\eta = 0.5\,\Delta_{\cap}$.~~
   **DERIVED 2026-05-24**: `DERIVED_ETA_COUPLING = c_polymer / A_min = 2 / 4
   = 1/2 ∈ ℚ`, with `c_polymer = BALABAN_POLYMER_RESIDUAL` (heuristic,
   refinable) and `A_min = WILSON_LOOP_MIN_AREA_DIMENSIONLESS` (from
   project spec, outline §7.1).  See `notes/sigma-hat-derivation.md` and
   `notes/fiducials_notes.md` §5–6.
4. **P1.2/P1.3 heat-kernel normalization audit.** ~~The current notes
   carry both inverse-coupling and diffusion-time language. Since a
   genuine heat kernel $K_t$ on a compact group concentrates at the
   identity as $t\downarrow 0$ and tends to Haar as $t\to\infty$, the
   use of `t = 2N/g^2` as heat-kernel time must be audited before
   character-expansion constants are treated as probability bounds.
   The buffer-shell note already exposes the related Haar-floor issue.~~
   **RESOLVED 2026-05-24.** (a) The CANONICAL / WILSON usage was
   clarified as inverse-coupling activity-exponent (3.2-upgrade);
   (b) the buffer-shell Haar-floor was given a uniform-in-$g$
   resolution via `BufferShellBound.uniform_value()` (a Haar floor +
   correctly-shaped tail term, with `TAIL_UNIFORM_PREFACTOR = 4`
   verified to dominate the direct heat-kernel integral over
   $\delta \in (0.02, 1.0)$, $g \in (0.05, 1.5)$ in both conventions).
   The legacy `value()` keeps the work_plan-spec $g^\beta$ shape but
   is no longer the uniform-in-$g$ reference; downstream consumers
   should use `uniform_value()`. See
   `notes/single-plaquette-derivation.md` §4 for the discussion.
5. **Lean sorries.** ~~`lean/SORRY_LEDGER.md` records the open
   `[P2.1]` and `[P2.3-{sf,lf,cap,sigma}]` obligations plus the
   assembled `step_obligation_witness`; all remain `sorryAx`-only.~~
   **As of 2026-05-24, all `[P2.3-{sf,lf,cap,sigma}]` and the assembled
   `step_obligation_witness` are CLOSED at `V = Q'` with axiom-gate
   `[propext]` only.  `[P2.1]` part (a) is also CLOSED; only part (b)
   (Conjecture 7.4 tightness) remains open.**  In addition, the global
   σ̂-budget closure framework `RationalTail.sigma_hat_budget_closure`
   is instantiated on the SU(2) pilot at finite truncation by
   `lean/YMGap/RG/SigmaHatPilot.lean::eta_pilot_budget_closes`
   (axiom-gate `[propext]`).
6. **Continuum limit, OS reconstruction, and the mass-gap theorem.**
   ~~These remain outside Phase 3 and are not implied by the pilot.~~
   **As of 2026-05-25 these are IN SCOPE** as Phases 7, 8, and 9
   respectively. Their analytic preconditions (genuine infinite-tail
   closure, chaining estimate, polymer activity domination at the type
   level) are scoped as Phase 6 (Lean-level analytic closures and
   tightenings). The goal is a constructive SU(2) mass-gap theorem;
   Phase 10 then sets up the extension to SU(3).

## Suggested next milestone

> **Status note (2026-05-25):** Phases 0–4 are closed; Phases 6–10 are
> the new in-scope work. The recommended near-term targets are:
>
> 1. **Phase 5.1** (reduction-theorem paper draft) — can begin now,
>    purely a write-up of the Phase-3 closure.
> 2. **Phase 6.1** (polymer-level activity-domination lemma) — formal
>    Lean closure of `[P2.1]` part (b); the empirical 2026-05-25 evidence
>    package supplies the analytical skeleton.
> 3. **Phase 6.2 + 6.3 + 6.4** (Q'.pow, UV-direction trajectory,
>    genuine infinite-tail closure) — the natural Phase-4-prep cluster
>    that unlocks Phase 7.
> 4. **Phase 6.5** (chaining estimate) — independent of (2)–(3); can
>    run in parallel.
>
> The legacy 3.2-upgrade text below is preserved as historical
> context.

### Milestone 3.2-upgrade — large-field character-expansion amplitude

**Goal.** Replace the placeholder $K_{\mathrm{lf}}=1.0$ by a
constructive SU(2) character-expansion residual bound, with an
explicit finite/convergent regime and exact rational constants where
possible.

**Preflight requirement.** Before changing `large_field_kp.py`, audit
the P1.2/P1.3 heat-kernel normalization: decide whether Phase 3 is
using inverse-coupling character weights, genuine diffusion-time heat
kernels, or a named canonical rescaling. Record the decision in
`notes/heat-kernel-normalization.md`, and update `buffer_shell.py` /
`notes/single-plaquette-derivation.md` if the probability-bound
interpretation changes.

**Deliverables.**

- `computations/large_field_kp.py` upgraded so `K_lf` is computed from
  the SU(2) character expansion rather than a fixed placeholder.
- `notes/large-field-derivation.md` updated with the exact residual
  estimate, convergence condition, and normalization choice.
- Tests covering finite/infinite large-field regimes, monotonicity in
  `g_k`, and propagation through `overlap_kp`, `sigma_hat_trajectory`,
  and `pilot_su2`.
- A Phase-3 sweep over the weak-coupling window showing where the five
  pilot criteria and the $\widehat{\sigma}_K \ge 0.5\widehat{\sigma}_0$
  threshold pass or fail.

**Why this is next.** It is the smallest scope-bounded move that
materially improves the pilot's honesty: it removes the last upstream
placeholder feeding $K_{\cap}$, and it tells us whether the current
small-field obstruction is the only quantitative obstruction in the
weak-coupling window.

**Recommended follow-up.** After 3.2-upgrade, close the Lean
`[P2.3-sf]` and `[P2.3-lf]` obligations against exact rational upper
bounds. Do not open Phase 4 or Phase 5 as primary work until
`K_lf`, $c_{\lambda}$ provenance, and the $\eta$ coupling have been
made explicit enough that the pilot is a numerical experiment rather
than a structural demo.
