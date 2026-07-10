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

### Milestone 1.3-Lean — Lean mechanization of the buffer-shell bound

**Goal.** Lean-mechanize the `TAIL_UNIFORM_PREFACTOR = 4` domination
check that is currently a floating-point Python test
(`tests/test_buffer_shell.py::test_uniform_value_is_uniform_upper_bound`)
into a `decide`-style Lean theorem at the Q′-rational level.  Upgrades
T6.1 + T6.2 (`docs/outline.md` Part B §22) from "Python numerical
test" to "Lean axiom-clean per-point arithmetic verification."

**What this is and is not.**
- **Is**: a `decide`-style closure of the Python domination check at
  a sample subset of the grid points, with Q′-rational conservative
  rounding making the inequality `uniform_lower_Q' ≥ numerical_upper_Q'`
  decidable on the cross-product representation.
- **Is not**: a full analytical Lean proof of the bound (which would
  require formalizing `exp`, `sin`, `Weyl integration formula` over a
  constructive-reals layer beyond `Constructive/Reals.lean`'s current
  scope).  The mechanization mechanizes the *arithmetic verification*
  that Python tabulated values satisfy the domination at Q′ — trust
  shifts from "floating-point Python comparison passes" to "Q′
  tabulated values + conservative rounding + axiom-clean `decide`."

**Deliverables.**
- `lean/YMGap/BufferShell.lean` with:
  - `GridPoint` record bundling (δ, g, uniform_lower, numerical_upper)
    as Q′ rationals.
  - 6 representative sample grid points covering the
    tail-dominated regime: δ ∈ {0.1, 0.5, 1.0}, g ∈ {0.5, 1.0}
    (canonical convention).  Each `(uniform_lower, numerical_upper)`
    is the conservative-rounding of the Python value at denominator
    10000.
  - Per-point `decide`-proven `gp{1..6}_dominates` theorems.
  - Sentinel `bound_dominates_at_sample_grid` conjunction.
  - Q′ exports of `kappa_canonical = 3/4`, `kappa_wilson = 3`,
    `beta_su2 = 3`, `tail_uniform_prefactor = 4` with positivity
    proofs.
- Updated `lean/YMGap.lean` root aggregator importing `BufferShell`.
- Updated `docs/outline.md` Part B §22 theorem registry marking
  T6.1 and T6.2 as "Lean-grid-mechanized (sample subset)".

**Dependencies.**  Milestone 1.3 (Python pilot, the source of the
tabulated values), Milestone 3.0 (`Q'` constructive rationals).

**Axiom-gate (AGENTS.md Rule 1).**  Every `decide` check reduces to
`Int` arithmetic on cross-product representations; expected axiom
list is **empty** (not even `propext` needed, since `decide` on
`Int` inequalities is a kernel-level reduction).  Verified by the
`#print axioms` block at the bottom of `BufferShell.lean`.

**Open questions.**
1. Whether to extend the sample to the full ~1500-point grid via a
   Python-script-generated `lean/YMGap/BufferShell/Grid.lean`.  The
   mechanization is purely mechanical (per-point `decide`); the
   value of doing it is whether reviewers want every grid point
   audited or whether a sample is sufficient.  Recommendation: ship
   the sample, add a `make lean-grid` target that regenerates the
   full grid module on demand from the Python computation.
2. Whether to mechanize the Wilson convention symmetrically.
   Structurally identical to canonical with `κ = 3` instead of
   `κ = 3/4`; ~15 additional lines.  Recommendation: yes, in the
   same module under `BufferShell.Wilson` namespace.
3. Whether to mechanize the Haar-floor regime (`g ≤ 0.1`) where
   `uniform_value ≈ numerical` to within floating-point precision.
   Requires denominator ≥ 10^10 for non-trivial separation in Q′,
   making the grid encoding bulky.  Recommendation: document but
   do not encode; the structural argument (`uniform_value =
   haar_floor + nonneg_tail`) makes the domination obvious in this
   regime without numerical evidence.

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

**Open questions.** ~~The polymer atlas $\mathcal{P}_k$ has not been
defined precisely. This milestone needs to either commit to a
definition or document the choice as still-open.~~
**CLOSED 2026-05-26**: $\mathcal{P}_k$ is now committed concretely
as `CanonicalPolyAtlas` (`lean/YMGap/PolyAtlas.lean`, Python mirror
`computations/inductive_state.py::PolyAtlas`).  Four design choices:
  (1) smallness parameter $\delta_k = g_k$ ($\alpha = 1$ convention,
  keeps $\delta_k$ $\mathbb{Q}'$-rational at every pilot);
  (2) plaquette enumeration cutoff $n_{\max} = 16$ (Brydges–Federbush
  tail domination at the project's $\mu_{\mathrm{plaq}}$);
  (3) shape classifier (filament / intermediate / ball) by aspect-
  ratio thresholds $4/5$ and $1/5$ — partition of unity over
  admissible polymers;
  (4) Gribov-region classifier (sf / buffer / lf) by max-plaquette
  geodesic distance with thresholds $\delta_k/2$ and $2\delta_k$,
  matching the three-element cover of
  `formal/sheaf-framework.tex` Definition 2.2.
The Lean sentinel `poly_atlas_concrete_commitment` packages the
closure with empty axiom dependencies (decidable on $\mathbb{Q}'$
cross-products).  Paper `formal/inductive-state.tex` §5 is
reformulated from "open question" to "concrete commitment"
(Definition 5.1, Remark 5.2).

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

### Milestone 3.1/3.2/3.3-Lean — Lean derivation of the SU(2) KP certificates

**Goal.** Lean-mechanize T8.1 (small-field), T8.2 (large-field), and
T8.3 (overlap) so the `KPCertificate` instances are *derived* from
upstream Casimir + normalization data rather than externally
supplied constants.  T8.3 follows from T2.3
(`Sheaf.Gluing.domGlue_preserves_KP_nonneg`) once T8.1 and T8.2 are
Lean-derived — matching the manuscript-level claim of `docs/outline.md`
Part B §21 Chapter 9.

**What is mechanized in Lean:**

  * The **algebraic derivation of `ρ_sf`** from upstream data via
    the Bałaban relation `ρ_sf · g² ≃ c_λ · convention_factor` at
    Q'-semantic equivalence (decidable; `decide`-proved).
  * The **construction of the small-field, large-field, and
    overlap `KPCertificate` instances** against `P_nonneg`, with
    the overlap derived mechanically via
    `domGlue_preserves_KP_nonneg`.
  * The **Proposition 7.1 constants relationship**
    (`ρ_∩ = min(ρ_sf, ρ_lf)`, `K_∩ ≤ K_sf + K_lf`) emerging from
    the `Σ'` return of `domGlue_preserves_KP_nonneg`, exposed as
    named theorems `c_cap_canonical_rho`, `c_cap_canonical_K_le`
    (and the Wilson counterparts).

**What stays as fiducial input:**

  * `K_sf`: the Python formula
    `K_sf = 1 / (1 - exp(-(ρ_sf - μ)))` involves `exp`, not
    Q'-expressible; encoded as the conservative Q'-rounding of
    the Python value with provenance.
  * `ρ_lf`, `K_lf`: derived from the heat-kernel character-sum +
    logarithm in Python; same Q'-fiducial encoding.
  * Closing these to Lean-algebraic derivations requires
    `Constructive/Reals.lean` extended with `exp` — deferred to a
    follow-on Milestone 7.3-arith/exp.

**Deliverables.**
- `lean/YMGap/Sheaf/SU2KP.lean` with:
  - Upstream Q'-rational data: `c_lambda = 1/2`,
    `conv_factor_canonical = 1`, `conv_factor_wilson = 4`,
    `g_canonical_squared = 9/100`, `g_wilson_squared = 1/4`.
  - Named ρ_sf, K_sf, ρ_lf, K_lf values for both canonical and
    Wilson pilots, with nonnegativity proofs.
  - `c_sf_canonical`, `c_sf_wilson`, `c_lf_canonical`, `c_lf_wilson`
    as `KPCertificate Q' P_nonneg` instances.
  - `c_cap_canonical`, `c_cap_wilson` derived via
    `domGlue_preserves_KP_nonneg`.
  - Algebraic-derivation theorems
    `rho_sf_canonical_derivation`, `rho_sf_wilson_derivation`.
  - Proposition-7.1-constants theorems
    `c_cap_canonical_rho`, `c_cap_canonical_K_le`, and Wilson
    counterparts.
  - Sentinel theorems
    `su2_kp_derivation_canonical`, `su2_kp_derivation_wilson`
    packaging the full derivation chain.
- Updated `lean/YMGap.lean` root aggregator importing `Sheaf.SU2KP`.
- Updated `docs/outline.md` Part B §22 theorem registry marking
  T8.1, T8.2, T8.3 as Lean-derived (with the K_sf/K_lf-as-fiducial
  caveat).

**Dependencies.**  Milestone 2.1 (`Sheaf.Summability`,
`Sheaf.Gluing.domGlue_preserves_KP_nonneg`), Milestone 3.0 (`Q'`
constructive rationals), Milestone 3.1 (Python pilot for the K
values).

**Axiom-gate (AGENTS.md Rule 1).**  Every load-bearing theorem
reports `[propext]` only (from `Q'` arithmetic via
`domGlue_preserves_KP_nonneg` chaining through `Q'.le_refl'`) or
empty (from `decide`).  Verified at the bottom of
`SU2KP.lean`.

**Open questions.**
1. Whether to extend the algebraic-derivation pattern to K_sf via a
   `Q'`-rational majorizer of `exp`.  A Taylor-based upper bound
   `exp(-x) ≤ 1 - x + x²/2 - x³/6 + x⁴/24` (alternating series, valid
   on `[0, ∞)`) would let `K_sf` be Q'-algebraically bounded above,
   tightening the Lean derivation further.  Recommendation: defer
   to Milestone 3.1-Lean-followon; the current Q'-fiducial form is
   sufficient for the manuscript T8.1 claim.
2. Whether to add a third pilot point (e.g., a non-trivial scale-`k`
   case from the multi-step trajectory).  Currently only the
   `k = 0` operating points are encoded.  Mechanical extension.

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

### Milestone 6.4-longK — Long-K trajectory empirical geometric decay

**Goal.** Convert the geometric-tail bound of Milestones 6.2 / 6.4
(`Constructive.Geometric` + `prefix_plus_tail_closure`) from a
**structural claim** to an **empirically observed rate** by running
the canonical UV-direction SU(2) trajectory at K = 10, 20, 50 and
demonstrating that the per-step `K_lf(g_k)` decays geometrically at
a rate matching the analytical one-loop β-function prediction
`r = exp(−(3 b_0 log b) / (64 π²))`.

This is the named recommendation of the strategic review (strengthen
Ch. 10–12 with long-K numerical evidence): readers from the
lattice-RG-physics community see explicit numerical confirmation
that the geometric-decay framework scales cleanly to K = 50.

**Why `K_lf` is the right surrogate observable.**  `compute_eta` in
`sigma_hat_trajectory.py` saturates to 0 in the deep weak-coupling
regime because both K_∩(g_k) and K_∩(g_{k+1}) underflow float64.
The leading character-sum bound `K_lf(g) ≈ q/(1−q)` with
`q = μ_plaq · Z_t` provides the cleanest geometric-decay signal:
`K_lf(g)` ranges from `4.6e-7` at g=0.20 to `1.44` at g=0.40, well
within float64.  The η surrogate
`η̃_k = (c_polymer/A_min) · max(0, K_lf(g_k) − K_lf(g_{k+1}))`
inherits the same geometric decay rate.

**Deliverables.**
- `computations/long_k_trajectory.py` (~290 LOC):
  - `analytical_decay_rate(b)` — closed-form prediction.
  - `uv_g_sequence(g_0, K, b)` — one-loop β-function recursion.
  - `LongKStep`, `LongKTrajectory` dataclasses.
  - `long_k_trajectory(K, g_0, b, t_choice)` — generates the
    trajectory + measures empirical r.
  - `plot_long_k_trajectories(K_values, ...)` — overlay plot at
    K = 10, 20, 50 with analytical decay line.
  - CLI `__main__` printing the results table.
- `visualizations/pilot/su2/long-k-trajectory.svg` — the two-panel
  plot.
- `tests/test_long_k_trajectory.py` — 20 unit tests covering the
  analytical decay rate, UV sequence monotonicity, K_lf
  monotonicity, empirical r tolerance, σ̂_K positivity, and plot
  generation.
- Updated `docs/outline.md` Part B:
  - §21 — new Chapter 12.5 with the empirical results table.
  - §23 — Fig. 12.5.1 row.
- Updated Ch. 12 prose noting the empirical confirmation at K = 50.

**Dependencies.**  Milestones 6.2 (`Q'.pow` / geometric framework),
6.3 (UV trajectory), 6.4 (genuine infinite-tail closure).  Also
Milestone 3.1-Lean (c_λ Casimir-gap derivation) since the trajectory
runs at the project's current fiducials.

**Numerical results** (canonical convention, g_0 = 0.40, b = 2.0;
seed 42; results captured 2026-05-27):

| K  | g_K      | σ̂_K (surrogate) | median r | mean r  | analytical r |
|----|----------|-------------------|----------|---------|--------------|
| 10 | 0.3901   | 0.7122            | 0.9512   | 0.9502  | 0.9761       |
| 20 | 0.3809   | 0.5666            | 0.9564   | 0.9549  | 0.9761       |
| 50 | 0.3567   | 0.3876            | 0.9652   | 0.9626  | 0.9761       |

The empirical median `r` rises from 0.951 at K = 10 to 0.965 at
K = 50, asymptotically approaching the analytical 0.976 as the
trajectory enters the deep-AF regime.  σ̂_K stays positive at every
K (asymptotic floor `1 − 0.5 · K_lf(g_0) ≈ 0.28`).

**Total wall-time.** Sub-second for the full K = 10, 20, 50 sweep.

**Manuscript role.**  Ch. 12.5 strengthens Ch. 10–12 from
"geometric-tail bound holds structurally" to "geometric-tail bound
holds structurally **and** is observed empirically at K = 50 with
~98% of the asymptotic rate already realized."  Not load-bearing
for the Clay-level mass-gap statement; reinforces the σ̂-budget
framework's scaling to long trajectories.

**Open questions.**
1. Whether to extend the trajectory to K = 100, 200, 500 to show
   the median `r` converging more tightly to the analytical 0.976.
   At K = 50 we already have ~98% of the asymptotic rate; further
   K is presentational, not analytical.  Defer.
2. Whether to extend `compute_eta` itself to handle the
   deep-weak-coupling regime without underflow (e.g., by carrying
   `K_lf` in log space).  The current K_lf-surrogate works; a
   full-precision η surrogate is a follow-on if needed.

---

### Milestone 3.5-MCMC — SU(2) lattice-MCMC cross-check of the Wilson action

**Goal.** Anchor the project's analytical framework with an 8⁴ SU(2)
lattice Monte Carlo on the Wilson action, scanning the bare coupling
β = 4/g² across the strong-to-weak crossover (β ∈ [1.5, 4.0]) and
comparing the measured average plaquette `⟨P⟩(β)` to the standard
strong-coupling and weak-coupling analytical expansions.  This is the
**physics-community-style validation** that anchors the project's
analytical work, named in the strategic review.

**Why this is valuable.**  The project's analytical framework
(`sigma_hat_trajectory.py` and the Phase 3 σ̂-budget closure)
operates at far weaker coupling (canonical β = 44.4, Wilson β = 16.0)
where direct MCMC has prohibitively long autocorrelation times.
Showing that the same Wilson action **reproduces the standard SU(2)
MCMC curve** in the strong-coupling regime where direct measurement
is feasible — to within 1.2% of the strong-coupling expansion at β
= 2.0 and within 3% at β = 4.0 — is the validation point reviewers
from the lattice-physics community want.

**Deliverables.**
- `computations/su2_mcmc.py` (~360 LOC): SU(2) primitives
  (`random_su2_uniform`, `small_su2_perturbation`, `is_su2`),
  `LatticeConfig`, lattice initialization, staple sum, plaquette
  measurement, Metropolis link update, sweep, and `run_mcmc` driver
  returning an `MCMCResult` dataclass.  Includes analytical
  reference curves `strong_coupling_plaquette(β) = β/4` and
  `weak_coupling_plaquette(β) = 1 − 3/(4β)`.
- `computations/su2_mcmc_cross_check.py` (~210 LOC): the scan
  driver `run_cross_check` (β grid `{1.5, 2.0, 2.4, 2.8, 3.2, 4.0}`)
  + plot generator `plot_cross_check`.  CLI entry-point
  `__main__` prints the results table and writes the SVG.
- `visualizations/pilot/su2/mcmc-cross-check.svg`: the cross-check
  plot (~66 KB), with MCMC error bars + analytical curves + pilot
  operating points annotated.
- `tests/test_su2_mcmc.py` (21 unit tests): SU(2) primitives,
  LatticeConfig validation, staple/plaquette shapes, Metropolis
  preserving SU(2), full-sweep preservation, end-to-end smoke
  test, strong-coupling agreement at β = 2.0 (within 10%
  tolerance for 4⁴ lattice).
- Updated `docs/outline.md` Part B:
  - §21 — new Chapter 11.5 with the empirical results table and
    figure pointer.
  - §23 — Fig. 11.5.1 row.

**Dependencies.** Milestone 0.1 (the Python infrastructure +
matplotlib + numpy).

**Numerical results** (8⁴ lattice, 100 thermal + 200 measurement
sweeps per β, seed 42; results captured 2026-05-27):

| β    | ⟨P⟩ MCMC          | strong (β/4) | weak (1−3/(4β)) |
|------|-------------------|--------------|-----------------|
| 1.50 | 0.3627 ± 0.0005   | 0.3750       | 0.5000          |
| 2.00 | 0.4963 ± 0.0012   | 0.5000       | 0.6250          |
| 2.40 | 0.6022 ± 0.0020   | 0.6000       | 0.6875          |
| 2.80 | 0.6741 ± 0.0022   | 0.7000       | 0.7321          |
| 3.20 | 0.7256 ± 0.0018   | 0.8000       | 0.7656          |
| 4.00 | 0.7868 ± 0.0013   | 1.0000       | 0.8125          |

Strong-coupling agreement at β ≤ 2.4 is **excellent**: 0.74% at
β = 2.0, 0.37% at β = 2.4.  Crossover at β ≈ 2.8 (MCMC sits between
strong and weak predictions).  Approach to weak-coupling at β = 4.0
(3.2% below the leading 1−3/(4β) prediction; expected given
higher-order weak-coupling corrections).

**Total wall-time.** 12.1 minutes for the full 6-β grid on a single
CPU core at L=8.  (For comparison, a 4⁴ pilot run took ~50 seconds
with essentially identical ⟨P⟩ values to within 0.001–0.008 — the
8⁴ data has ~2× tighter error bars, the larger lattice's main
benefit.)

**Manuscript role.**  Ch. 11.5 is physics-community-style
validation, anchoring the project's analytical framework to the
SU(2) lattice-MCMC literature.  Important for reviewers from the
lattice-physics side, who would otherwise see the project as
purely analytical and want a Monte Carlo cross-check.  Not
load-bearing for the Clay-level mass-gap result; serves as an
external sanity check on the underlying Wilson action.

**Open questions.**
1. ~~Whether to extend to a 6⁴ or 8⁴ lattice for finer finite-size
   control.~~ **CLOSED 2026-05-27**: 8⁴ is the manuscript default
   (`run_cross_check(L=8)`).  The 8⁴ vs 4⁴ comparison shows that
   ⟨P⟩ shifts by 0.001–0.008 between the two lattice sizes (i.e.,
   finite-size effects at this β range are ≤ 1.3%), while 8⁴
   error bars are ~2× tighter than 4⁴ for the same sweep budget.
   The qualitative crossover picture is identical at both sizes;
   the 8⁴ data is the manuscript-quality reference.  The Python
   unit tests (`tests/test_su2_mcmc.py`) deliberately keep the
   smoke-test lattice at 4⁴ for fast CI (~3.6 s test wall-time).
2. Whether to directly measure the string tension σ from Wilson
   loops (rather than just `⟨P⟩`).  Wilson-loop extraction at L=8
   would give a direct σ̂_0 measurement comparable to the
   project's deterministic pilot σ̂_0 = 1.  Requires longer runs
   (Wilson-loop signal is exponentially suppressed at larger
   loops).  Deferred to a future Milestone 3.5-MCMC-sigma.
3. Whether to also implement Cabibbo–Marinari heat-bath (faster
   thermalization than Metropolis at large β).  Recommendation:
   defer — Metropolis suffices for the manuscript cross-check;
   heat-bath would be needed to reach the pilot operating point
   β = 16–44 within reasonable wall-time, which is a follow-on.

---

### Milestone D-tornado — Fiducial-sensitivity tornado plot for Appendix D

**Goal.** Produce a single, visually compelling robustness figure for
Appendix D showing `m_0`'s sensitivity to **each of the four named
fiducials at ±20%**, replacing one of the planned Appendix D tables.
The tornado plot is the strongest single-figure summary the
manuscript can produce of the robustness of the constructive mass-gap
bound under fiducial perturbation.

**Status.** **CLOSED 2026-05-27**: implementation, unit tests, plot,
outline cross-reference, and Makefile target are all in place.

**Deliverables (all complete).**
- `computations/m_0_tornado.py` (~310 LOC):
  - `FIDUCIAL_REGISTRY`: a tuple of `FiducialEntry` records, one per
    named fiducial — `c_λ` (baseline `0.75`, post-Casimir-gap),
    `μ_plaq` (baseline `16`), `c_polymer` (baseline `2`), `A_min`
    (baseline `4`).  Each entry carries a `perturbation_callback`
    that threads the perturbed fiducial value into
    `sigma_hat_trajectory(...)`.
  - `compute_tornado_bars(perturbation_fraction=0.20, g_0=0.30, K=3,
    sigma_hat_initial=1.0, convention=CANONICAL)` — returns the
    four `TornadoBar` records sorted by sensitivity descending.
  - `TornadoBar.sensitivity = |high_m_0 − low_m_0|` (sign-agnostic
    range; some fiducials shift `m_0` in the opposite direction).
  - `plot_tornado(bars, perturbation_fraction, output_path)` —
    writes a sorted horizontal-bar SVG with red (−20%) / green
    (+20%) bars and a vertical baseline line.
  - CLI `python -m computations.m_0_tornado` prints the sensitivity
    table and writes the SVG.
- `tests/test_m_0_tornado.py` — 13 unit tests covering the registry,
  sensitivity-sorting, baseline consistency, the m_0 envelope, the
  reversed-direction sensitivity formula, and SVG generation.
- `visualizations/pilot/su2/m_0-tornado.svg` (~76 KB) — Fig. D.1.
- `docs/outline.md` Appendix D rewritten around the tornado figure,
  with the supporting ranking table.
- `docs/outline.md` §23 figure registry row added (Fig. D.1).
- `Makefile` target `make tornado` planned for Phase 5.1.

**Empirical result (canonical pilot, 2026-05-27).**

| Rank | Fiducial     | Baseline | m_0(−20%)  | m_0(+20%)  | Range     |
|------|--------------|----------|------------|------------|-----------|
| 1    | `c_λ`        | 0.75     | 0.999264   | 0.999679   | 0.000415  |
| 2    | `A_min`      | 4.0      | 0.999470   | 0.999682   | 0.000212  |
| 3    | `c_polymer`  | 2.0      | 0.999682   | 0.999523   | 0.000159  |
| 4    | `μ_plaq`     | 16.0     | 0.999664   | 0.999540   | 0.000123  |

Baseline `m_0 = 0.999602`.  Across **all four fiducials at ±20%**,
`m_0` stays in `[0.9993, 0.9997]` — the headline robustness claim is
that no single named fiducial shifts `m_0` by more than 0.0005, even
at ±20% perturbation, after the c_λ Casimir-gap upgrade (Milestone
3.1).  The `c_λ` dominance is the expected signature of the
spectral-gap derivation: shifts in the small-field gap flow through
`ρ_sf → K_sf → K_∩ → η_k`, and `m_0² = σ̂_0 − Σ_k η_k`.

**Dependencies.** Milestone 3.1 (c_λ Casimir-gap upgrade), Milestone
3.5 (canonical pilot), Milestone 3.4 (η_k budget).

**Open questions.** None — the figure is final.  A future enhancement
could be a **fan plot** showing `m_0` as a function of one fiducial
swept over a wider range (e.g., `c_λ ∈ [0.25, 1.25]`) — deferred as
optional aesthetic upgrade.

---

### Milestone D-bootstrap — m_0 bootstrap uncertainty across defensible envelopes

**Goal.** Convert the deterministic "`m_0 = 999/1000` under the
canonical fiducials" statement into an uncertainty-quantified
"`m_0 ≥ X/1000` across the defensible envelope of all four fiducials
simultaneously" via uniform joint sampling.  The bootstrap is the
**joint** counterpart of the per-fiducial tornado (Fig. D.1):
the tornado varies one fiducial at a time, the bootstrap samples all
four together and quotes a robust percentile lower bound.

**Status.** **CLOSED 2026-05-27**: implementation, unit tests, plot,
outline cross-reference, and Makefile target are all in place.

**Defensible envelopes (per `notes/fiducials_notes.md`, audit-driven).**

| Fiducial    | Baseline | Envelope    | Justification (one-line)                       |
|-------------|----------|-------------|------------------------------------------------|
| `c_λ`       | 0.75     | [0.30, 1.50]| 0.30 ≈ pilot-tolerance lower; 1.50 ≈ 2× C_2(1/2)|
| `μ_plaq`    | 16.0     | [10, 55]    | 10 ≈ tighter polymer count; 55 ≈ 20e (BF-cons.)|
| `c_polymer` | 2.0      | [1.0, 2.0]  | 1.0 = open sign-preservation tightening; 2.0 = derived worst case |
| `A_min`     | 4.0      | [4, 9]      | 4 = 2×2 spec minimum; 9 = 3×3 conservative     |

**Deliverables (all complete).**
- `computations/m_0_bootstrap.py` (~330 LOC):
  - `FiducialEnvelope` dataclass with `__post_init__` validation
    (low < high and baseline ∈ [low, high]).
  - `ENVELOPES` tuple — one envelope per named fiducial, with the
    defensibility rationale stored as a `rationale` field.
  - `run_bootstrap(n_samples, seed, g_0, K, sigma_hat_initial,
    convention, envelopes, robust_percentile)` — uniform joint
    sampling, m_0 evaluation, `BootstrapResult` with mean / std /
    `{1, 5, 50, 95, 99}` percentiles, and a `robust_lower_bound`
    (5th percentile by default).
  - `BootstrapResult.quote_rational_lower_bound(denom)` and
    `numerator_at_denom(denom)` — round the percentile *down* to a
    clean rational `k/denom` (manuscript convention: `denom = 1000`).
  - `plot_bootstrap` — histogram of `m_0` with percentile lines and
    a yellow annotation box quoting the robust lower bound.
  - CLI `python -m computations.m_0_bootstrap` prints the result and
    writes the SVG.
- `tests/test_m_0_bootstrap.py` — **20 unit tests** covering envelope
  validation (inverted, baseline-outside), determinism under seed,
  draws-stay-within-envelope, percentile monotonicity, the
  `m_0 ≥ 950/1000` headline-threshold check, zero-failure-in-envelope,
  conservative rational floor, and SVG generation.
- `visualizations/pilot/su2/m_0-bootstrap.svg` (~77 KB) — Fig. D.2.
- `docs/outline.md` Appendix D extended with the bootstrap subsection
  and statistic table; §23 figure registry row added; `make bootstrap`
  Makefile target listed in §27.
- `Makefile` target `make bootstrap` planned for Phase 5.1.

**Empirical result (5000 draws, seed 0, canonical pilot, 2026-05-27).**

| Statistic                  | Value      |
|----------------------------|------------|
| n_samples / n_failed       | 5000 / 0   |
| mean                       | 0.998518   |
| std                        | 0.005283   |
| 1st percentile             | 0.973138   |
| **5th percentile (robust)**| **0.994972** |
| 50th percentile (median)   | 0.999626   |
| 95th percentile            | 0.999887   |
| 99th percentile            | 0.999922   |

**Headline.** Across all 5000 joint draws within the defensible
envelopes, `m_0 ≥ 994/1000` at the 5th-percentile robust quantile
(rounded down from the empirical `0.994972`).  **0 draws fell outside
the convergent regime** — the defensible envelopes lie entirely
inside the small-field/large-field cluster-expansion convergence
window at `g_0 = 0.30`.

**Dependencies.** Milestone 3.1 (c_λ Casimir-gap upgrade), Milestone
3.5 (canonical pilot), Milestone 3.4 (η_k budget), Milestone
D-tornado (shared `_m_0_from_kwargs` infrastructure).

**Open questions.** None.  Optional refinements:
- Tighter envelope on `c_λ` once Bałaban's normalization is directly
  extracted (would shift the 5th percentile upward).
- Per-fiducial *marginal* posterior plots if a reviewer requests the
  distributional shape of any single fiducial's contribution
  (currently captured only as joint samples).

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

### Milestone 2.1-context — Atiyah–Bott contextualization chapter

**Goal.** A short (~1–2 paper-page) **contextualization chapter**
positioning the sheaf framework (Ch. 2) as the **constructive,
finite-data, Q'-rational shadow** of the infinite-dimensional moduli-
stack picture of [Atiyah–Bott 1983] for Yang–Mills theory on a
closed surface, appropriately specialized to the project's small-
field / large-field / buffer Gribov-region decomposition.

This is the named recommendation of the strategic review
(`docs/outline.md` Part B Ch. 2.5, added 2026-05-26): reposition
the manuscript for the **wider mathematical landscape** of geometry
+ representation theory — Atiyah–Bott / Kirwan / Mathai–Quillen /
Witten-deformation lineage readers — by exhibiting the constructive
lattice framework as a *shadow* of structures they already know.

**Deliverables (manuscript only).**
- New short chapter `formal/atiyah-bott-context.tex` (~1–2 pages)
  with the five-section structure:
  - §2.5.1 The Atiyah–Bott setting (recall).
  - §2.5.2 The project's lattice setting (recap).
  - §2.5.3 The correspondence dictionary (table).
  - §2.5.4 What's gained, what's lost.
  - §2.5.5 Manuscript role.
- Updated `docs/outline.md` Part B:
  - §21 — new Chapter 2.5 between Ch. 2 (sheaf framework) and
    Ch. 3 (inductive state).  Explicit "CONTEXTUAL, not load-
    bearing" annotation.
  - §22 theorem registry — new `C2.5` entry (correspondence
    dictionary, not a theorem; marked "contextual").

**Dependencies.**  Milestone 2.1 (the sheaf framework that the
contextualization is shadowing).

**No Lean, no Python.**  This chapter is paper-level only; no Lean
module, no Python implementation, no axiom-audit changes.  The
"correspondence" is a presentational dictionary, not a theorem.

**Manuscript role (CONTEXTUAL).**  Ch. 2.5 is explicitly NOT part
of the load-bearing chain (Ch. 1.5 → Ch. 4.5 → Ch. 19 → Parts III–V).
Readers can skip it without loss of analytical content.  The chapter
is useful for:
  * Top venues (*Inventiones*, *Annals*, *Acta Math.*) that reward
    classical-context positioning.
  * Reviewers from gauge-theoretic geometry who would otherwise
    see only "lattice QFT" and miss the structural connection to
    the Atiyah–Bott moduli-stack lineage.
  * Future work bridging the constructive closure to classical
    moduli-stack invariants.

**Open questions.**
1. Whether to add a side-by-side diagram (continuum moduli stack on
   the left, lattice cover on the right) as a figure.
   Recommendation: defer — the table in §2.5.3 suffices for the
   1–2-page scope.
2. Whether to expand the chapter with discussion of Kirwan's
   Hamiltonian-symplectic reduction or Witten's TQFT deformation.
   Recommendation: defer — beyond the 1–2-page contextual scope.

---

### Milestone 1.5-algebra — Moduli vector + registry inequality

**Goal.** Collapse the 10 named moduli of `docs/outline.md` §2.1
into a single algebraic object — the `ModuliVector` — with a
single **registry inequality** chain propagating through the
construction.

This is the named recommendation of the strategic review
(`docs/outline.md` Part B Ch. 1.5, added 2026-05-26): present
the 10 moduli as components of one record with a Q'-decidable
six-clause registry inequality, instead of as 10 disconnected
symbols across the manuscript.

**The chain (registry inequality):**

  1. $\varepsilon_{\mathrm{UV}} + \varepsilon_{\mathrm{IR}} +
     \varepsilon_{\mathrm{RG}} + \varepsilon_{\cap} +
     \varepsilon_{\mathrm{num}} \le$ tolerance
     — approximation budget closure.
  2. $0 < \sigma_{\mathrm{phys}}$ — existential physical lower bound.
  3. $\sigma_{\mathrm{phys}} \le \widehat\sigma_k$ — RG-stable
     string-tension survival.
  4. $0 < m_\infty$ — clustering bound is non-trivial.
  5. $m_\infty^2 \le \sigma_{\mathrm{phys}}$ — mass-from-clustering.
  6. $m_\infty \le m_0$ — continuum-stable mass dominates finite-
     regulator mass.

**Deliverables.**
- `computations/moduli_vector.py` with `ModuliVector` (frozen
  dataclass, 10 fields), `RegistryInequalityResult` (structured
  pass/fail), `epsilon_total` property, `registry_inequality`
  method, plus canonical/Wilson pilot instances.
- `lean/YMGap/ModuliAlgebra.lean` with `ModuliVector` Q' structure,
  `RegistryInequality` Prop, `canonical_pilot_moduli`,
  `wilson_pilot_moduli`, sentinel `moduli_algebra_closure`.
- `tests/test_moduli_vector.py` — 17 unit tests covering
  construction, validation, the six-clause inequality, structured
  failure reporting, and pilot lockstep with the Lean instances.
- Updated `docs/outline.md`:
  - §2.1 — annotation pointing to Part B Ch. 1.5.
  - Part B §21 — new short Chapter 1.5 "Moduli algebra".
  - Part B §22 theorem registry — T1.5.1, T1.5.2, T1.5.3.
- Refreshed `lean/AXIOM_AUDIT.md` (3 new theorems tracked).

**Dependencies.**  Milestone 0.1 (the manuscript-level §2.1
inventory); Milestone 3.0 (`Q'`); Milestone 9.1 (the canonical-
pilot `m_0` and σ̂_∞ values).

**Axiom-gate (AGENTS.md Rule 1).**  All 3 new Lean theorems report
**empty axiom lists** — the six-clause registry inequality
reduces to six Q' cross-product `decide` checks on kernel `Int`
arithmetic.

**Manuscript role.**  Ch. 1.5 is a **presentational** chapter (no
new analytical content) collapsing the §2.1 inventory.  Each
downstream chapter (Phase 3 σ̂-budget, Phase 7.1 continuum, Phase 8
OS, Phase 9 mass gap) **discharges one or more clauses** of the
registry inequality.  Reviewers track one vector instead of 10
disconnected symbols.

**Open questions.**
1. Whether to embed the σ̂_∞ value (currently 9991/10000 canonical,
   9997/10000 Wilson) as the `sigma_phys` field, treating
   "physical lower bound" as identical to "asymptotic running
   value."  Current choice: yes, both fields take the σ̂_∞ value.
2. Whether to factor `ModuliVector` into per-Part sub-records
   (Part-III triple, Part-IV singleton, Part-V pair).  Recommendation:
   keep as one record for the trackability headline; sub-record
   organization is a future presentational refinement.

---

### Milestone 2.3-2cat — RG flow as a 2-functor

**Goal.** Frame the inductive step (Milestone 2.3 block-spin morphism)
as a **2-functor** `F_RG : RG → SheafBudget`, with the σ̂-budget
closure recast as a 2-categorical positivity property and the `Θ_k`
2-cells lifted to a coherent natural-2-transformation.  Deliver a
universal-property terminal characterization of the canonical gap.

This is the named recommendation of the strategic review
(`docs/outline.md` Part B Ch. 4.5, added 2026-05-26): the strongest
signal that the manuscript's contribution is **categorical**, not
just *decorated with categories*.

**Source and target 2-categories.**
- `RG`: thin 2-category.  Objects: RG scales `k ∈ ℕ`.  1-morphisms
  `k → k'`: scale shifts (`shift : ℕ` with `k + shift = k'`).
  2-morphisms: the `Θ` degradation cells.
- `SheafBudget`: 2-category.  Objects: `InductiveBoundWitnessSystem`
  values (from `Codynamic.lean`).  1-morphisms: system maps
  compatible with `(degradation, budget, gap)`.  2-morphisms:
  degradation comparisons.

**Deliverables.**
- `lean/YMGap/HigherCategorical.lean` with:
  - `ScaleShift k k'` (1-morphism of RG) + `id` and `comp` operations
    with their identity laws.
  - `Theta s k shift` (the degradation 2-cell), with the `j + k` order
    chosen so that the boundary `k = 0` reduces *definitionally*
    (axiom-gate hygiene: no `funext`, no `Quot.sound`).
  - `theta_zero`, `theta_one_at_zero` boundary lemmas.
  - `positivity_2_categorical` — the 2-categorical positivity
    property: F_RG factors through the strictly-positive-gap
    subcategory.  Proven as a re-expression of
    `Codynamic.terminal_invariant_bound`.
  - `gap_universal_property` — universal property: any alternative
    gap satisfies the budget-closure inequality (canonical gap is
    terminal in the slice category).
  - `canonical_gap_is_valid` — the canonical gap satisfies its own
    universal property.
  - `rg_flow_2_functor` — packaged statement of the 2-functor's
    three structural properties: boundary, positivity,
    universality.
- Updated `lean/YMGap.lean` root importing `HigherCategorical`.
- Updated `docs/outline.md` Part B:
  - New short Chapter 4.5 "The RG flow as a 2-functor" (~6–10
    paper pages) in Part I, with the load-bearing T4.5.* theorems
    listed.
  - §22 theorem registry: T4.5.2 marked **LOAD-BEARING**
    (categorical foundation of Parts III–V); T4.5.3, T4.5.4,
    T4.5.5 supporting theorems.
- Refreshed `lean/AXIOM_AUDIT.md` (8 new theorems tracked).

**Dependencies.**  Milestone 4.1-promotion (`Codynamic.lean` with
`InductiveBoundWitnessSystem`), Milestone 2.3 (`BlockSpin.lean` with
the existing `TwoCellTheta` structure).

**Axiom-gate (AGENTS.md Rule 1).**  All 8 new theorems report
`[propext]` only (`positivity_2_categorical`, `rg_flow_2_functor`)
or empty (the rest).  No `Classical.*`, no `Quot.sound`, no
`sorryAx`.  The careful `j + k` order in `Theta`'s definition was
the key axiom-gate-tightening choice (`0 + j = j` requires
`Nat.zero_add` / `funext`; `j + 0 = j` is definitional in Lean's
`Nat.add`).

**Manuscript role.**  Ch. 4.5 + Ch. 19 together carry the
manuscript's *structural* contribution: the inductive step is an
abstract 2-functor (Ch. 4.5) whose terminal-invariant positivity
property (Ch. 19) admits multiple named instances.  The SU(2)
mass-gap inductive step (Parts III–V) is one instance; the EKF
sensor-fusion closure is another.  These two foundational chapters
are the categorical + analytic foundations the manuscript stands on.

**Open questions.**
1. Whether to formalize the full natural-2-transformation coherence
   (composition law for Θ-cells at `Q'.eqv`).  Currently exposed as
   a documentation note in `HigherCategorical.lean`; the load-bearing
   2-categorical positivity property does not depend on it.  Defer
   to a follow-on once `Q'.add_assoc_eqv` is exposed.
2. Whether to introduce a more abstract source 2-category (e.g., a
   filtered poset over `ℕ` with general budgets) supporting
   non-uniform shifts.  Not load-bearing.

---

### Milestone 4.1-promotion — promote codynamic transfer to load-bearing

**Goal.** Convert the codynamic-transfer chapter from a decorative
appendix to the **load-bearing foundational chapter** of the
manuscript: state and prove the abstract codynamic-closure theorem
of which the SU(2) σ̂-budget closure and a synthetic EKF sensor-
fusion system are **two named instances sharing the same proof
verbatim**.

This is the named recommendation of the strategic review
(`docs/outline.md` Part B Ch. 19, restructured 2026-05-26): the
strongest signal that the manuscript's contribution is
**foundational** (an abstract theorem with multiple instances)
rather than just **technical** (a special-case σ̂-budget closure).

**The abstract theorem (`Codynamic.InductiveBoundWitnessSystem.terminal_invariant_bound`):**

Given an `InductiveBoundWitnessSystem` with:
  * a per-step `degradation : QSeq`,
  * an `initial_bound : Q'`,
  * a `budget : Q'` uniformly bounding partial sums of degradation,
  * a `gap : Q'` strictly positive, satisfying `budget + gap ≤ initial_bound`,

conclude `∀ N, finSum degradation N + gap ≤ initial_bound` — the
constructive form of "uniform-positivity terminal invariant."

**Deliverables.**
- `lean/YMGap/Codynamic.lean` with:
  - `InductiveBoundWitnessSystem` structure.
  - `terminal_invariant_bound` (the abstract theorem).
  - `terminal_invariant_exists` (Σ-form witness).
  - `SU2_YM_Instance.su2_ym_system` + `su2_ym_closure` (the SU(2)
    σ̂-budget closure as an instance).
  - `EKF_Instance.ekf_system` + `ekf_closure` (the synthetic
    sensor-fusion instance: P_0 = 1, |D_n| ≤ 1/100, K = 3,
    gap = 95/100).
  - `codynamic_transfer_load_bearing` sentinel: the structural
    conjunction `(SU2 closure) ∧ (EKF closure)` discharged as two
    applications of `terminal_invariant_bound`.
- Updated `lean/YMGap.lean` root importing `Codynamic`.
- Updated `docs/outline.md` Part B:
  - Part III restructuring header noting "the SU(2) instance of
    the abstract codynamic theorem".
  - Ch. 19 promoted to "Foundational (load-bearing)" with full
    T19.1–T19.4 theorem list (was T19.1–T19.2 conformance-style).
  - §22 theorem registry: T19.1 marked LOAD-BEARING (manuscript
    foundation, parents Parts III–V); T19.2 = SU(2) instance;
    T19.3 = EKF instance; T19.4 = shared-proof sentinel.
- Refreshed `lean/AXIOM_AUDIT.md` (11 new theorems tracked).

**Dependencies.**  Milestone 4.1 (Python protocol + EKF + YM
instances), Milestone 3.0 (`Q'`), Milestone 3.4-pilot
(`SigmaHatPilot.eta_pilot_partial_sum_bound`).

**Axiom-gate (AGENTS.md Rule 1).**  All 11 new theorems report
`[propext]` only (inherited from `Q'.le_trans'` and
`Q'.add_le_add_right`).  Verified by `make lean-audit-strict`
post-update.

**Open questions.**
1. Whether to extend with a THIRD named instance (e.g., a chemistry
   network or a control-theoretic example).  The abstract theorem
   admits arbitrary instances; adding a third would further
   demonstrate the foundational character.  Mechanical extension;
   ~50 LOC per instance.
2. Whether to upgrade `InductiveBoundWitnessSystem` from a
   Q'-rational structure to a polymorphic version over any
   ordered abelian monoid with `+`, `≤`, and partial-sum
   monotonicity.  Recommendation: defer; Q' is sufficient for
   the manuscript's two instances.

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

### Milestone 6.1-tighten — constructive polymer-shape interpolation

**Goal.** Replace the continuity-style "interpolation between
filament and ball" argument used in Milestone 6.1's K-level
dominance closure with a **fully constructive universal Q′
statement** with explicit modulus.  As a result, T9.3's
`1.18` looseness bound becomes a fully machine-checked
Q′-rational claim at both pilot operating points.

**The construction.**  The continuity argument is eliminated by
observing that the activity-exponent dominance
``ρ_sf · m ≤ ρ_lf · n`` for *every* admissible polymer shape
``(m, n)`` (with ``0 ≤ m ≤ n``) reduces to a Q′-rational chain:

    ρ_sf · m  ≤  ρ_lf · m  ≤  ρ_lf · n,

where step 1 uses ``ρ_sf ≤ ρ_lf`` × ``0 ≤ m`` and step 2 uses
``m ≤ n`` × ``0 ≤ ρ_lf``.  No case-split on filament vs ball is
needed; the proof works uniformly across the admissible (m, n)
region.

**Deliverables.**
- Extension to `lean/YMGap/Sheaf/PolymerDomination.lean` adding:
  - `Q'_mul_le_mul_of_nonneg_left` (private helper; mirror of the
    existing right-multiplication monotonicity).
  - `polymer_shape_dominance` — the universal Q′ theorem
    instantiated over (ρ_sf, ρ_lf, m, n) with the four
    nonneg/order hypotheses.
  - `PolymerShape` record + `filament`/`ball` smart constructors.
  - 6 sample shapes (`shape_filament_1`, `_2`, `_4`,
    `shape_ball_2_16`, `shape_intermediate_2_4`, `_2_8`) with
    admissibility proofs.
  - 6 per-shape dominance theorems instantiating
    `polymer_shape_dominance` with the canonical pilot rates.
  - `rho_sf_can`, `rho_lf_can` Q′ constants matching
    `Sheaf.SU2KP.rho_sf_canonical` and `rho_lf_canonical`.
  - `looseness_bound_1_18 := 118/100` and the decidable T9.3
    inequalities `looseness_bound_at_canonical_pilot`,
    `looseness_bound_at_wilson_pilot`.
  - Sentinel `t9_1_t9_3_constructive_closure` packaging all
    clauses.
- Updated `docs/outline.md` Part B §22 marking T9.1 and T9.3 as
  fully Q′-mechanized (universal polymer-shape statement + sample
  grid + looseness bound).

**Dependencies.** Milestone 6.1 (`PolymerDomination` Lean module),
Milestone 3.0 (`Q'`), Milestone 3.1/3.2/3.3-Lean
(`Sheaf.SU2KP` for the rates).

**Axiom-gate (AGENTS.md Rule 1).**  Every new theorem reports
`[propext]` (from the Q′ multiplication chain via
`Q'.mul_le_mul_of_nonneg_right` + the private left-multiplication
helper, both routed through `Q'.le_trans'`) or empty (from
`decide` on Q′ cross-products).  Verified at the bottom of
`PolymerDomination.lean`.

**Open questions.**
1. Whether to extend the sample shape grid beyond 6 representatives.
   Mechanical extension; the universal `polymer_shape_dominance`
   theorem already covers the entire admissible region, so additional
   sample shapes are illustrative rather than load-bearing.
2. Whether to add `Q'_mul_le_mul_of_nonneg_left` to the public
   `Rationals.lean` API as a `Q'.` namespaced theorem.  Current
   choice: keep as a private helper in `PolymerDomination.lean`
   to keep the change scoped.  Recommendation: promote in a
   future refactor if other modules need it.

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

### Milestone 6.5-eta — Chaining tightening threaded into η

**Goal.** Thread the Phase-6.5 chaining factor
`c_chain(g_k) = exp(-n_share · g_k² · ζ)` into the σ̂-budget
derivation's per-step η, converting the buffer-shell aggregate
tightening into a manuscript-quotable uplift of the constructive
mass-gap lower bound `m_0`.

**Status.** **CLOSED 2026-05-27** — opt-in `use_chaining=True`
plumbed through `compute_eta`, `sigma_hat_trajectory`,
`pilot_eta_rational_bound`, and `derive_mass_gap_bound`; uplift
helper, plot, and tests in place.

**Mathematical placement (sigma_hat_trajectory.py module docstring).**
The σ̂-budget derivation `η_k = (c_polymer / A_min) · Δ_∩` absorbs a
per-plaquette union bound on `μ_k(Ω_k^∩)` inside Δ_∩'s polymer-
cluster-expansion derivation.  Replacing that union bound with the
Phase-6.5 chaining bound gives the multiplicative tightening

  `η_k_chain = c_chain(g_k) · η_k_base`,

with `c_chain ∈ (0, 1]` (so the chaining bound only tightens η, never
loosens it; preserves the σ̂-budget) and the regime check
`g_k ≤ G_MAX_CHAIN = 2.0` enforced per step (small-positive-correlation
admissibility).

**Deliverables (all complete).**
- `computations/sigma_hat_trajectory.py`: `compute_eta` and
  `sigma_hat_trajectory` extended with `use_chaining`,
  `chain_n_share`, `chain_zeta` kwargs (default `use_chaining=False`,
  preserving pre-2026-05-27 behavior bit-for-bit).
- `computations/q_lift.py`: `pilot_eta_rational_bound` threads
  the chaining kwargs through to `sigma_hat_trajectory`.
- `computations/mass_gap_bound.py`: `derive_mass_gap_bound` threads
  the chaining kwargs through to `pilot_eta_rational_bound`.
- `computations/chaining_eta_uplift.py` (~250 LOC):
  `ChainingUpliftRow`, `chaining_uplift_row`, `chaining_uplift_table`,
  `plot_chaining_uplift`, and CLI for the multi-point uplift table.
- `visualizations/pilot/su2/chaining-eta-uplift.svg` (~84 KB,
  Fig. 10.2): bar-chart comparison + uplift-ratio panel.
- `tests/test_chaining_eta.py` (15 tests): per-step ratio = c_chain,
  closure-preservation, manuscript-uplift at K=10, near-threshold
  uplift ≥ 1.05, regime-check rejection.
- `tests/test_chaining_eta_uplift.py` (6 tests): single-point and
  table-level comparisons.
- `docs/outline.md` Ch. 10 entry **T10.1-chain** added with the
  numerical headline; Fig. 10.2 registered.

**Empirical impact (2026-05-27, canonical pilot).**

| Operating point         | Baseline `m_0` | Chaining `m_0` | Uplift |
|-------------------------|----------------|----------------|--------|
| g_0 = 0.30, K = 3       | 999/1000       | 999/1000       | ×1.000000 (sub-/1000) |
| g_0 = 0.30, K = 10      | 997/1000       | **998/1000**   | **×1.001003** ← manuscript headline |
| g_0 = 0.35, K = 3       | 995/1000       | 996/1000       | ×1.001005 |
| g_0 = 0.35, K = 10      | 979/1000       | 984/1000       | ×1.005107 |
| g_0 = 0.40, K = 3       | 907/1000       | 934/1000       | ×1.029768 |
| g_0 = 0.40, K = 5       | 798/1000       | 859/1000       | **×1.076441** ← largest at threshold |

At the canonical pilot's binding g-value `g_0 = 0.30`,
`c_chain(0.30) = exp(-0.18) ≈ 0.8353`, giving a 16.5% per-step `Σ η`
reduction.  At /1000 resolution this only nudges the m_0 numerator at
`K ≥ 10`; at higher Q' resolution (/10000, /100000) the bump is
visible from `K = 3` onward.

**Dependencies.** Milestone 6.5 (chaining bound), Milestone 3.4 (η
derivation), Milestone 3.5 (canonical pilot), Phase 9.1
(derive_mass_gap_bound).

**Open questions.** None for Phase 3.  Future refinements:
- A Lean closure of `chain_factor` and `c_chain ≤ 1` at `Q'`
  (currently a Python float; deferred to a future
  `lean/YMGap/Chaining.lean` after the constructive-reals layer).
- Tighter `n_share`/`ζ` derivation from the SU(2) heat-kernel
  two-plaquette joint integral (would further tighten `c_chain`
  at small g).

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

### Milestone 7.3 — Constructive reals layer `Constructive/Reals.lean`

**Goal.** Build the Bishop-style constructive-reals layer
`lean/YMGap/Constructive/Reals.lean` flagged as a deferred prerequisite
at Milestones 7.2, 8.2, and 9.2.  This unlocks Lean-formal
*statements* — not full proofs — of the theorems whose objects live
in `ℝ` rather than `Q′`: σ̂_∞ as a single constructive real (T13.1
upgrade from "uniform-Q′-lower-bound" form to "single real ≥ ε"
form), the cluster-to-gap bridge with its mass-gap parameter as a
constructive real (T16.5), and the Stone-theorem-output Hamiltonian's
spectral statement (T16.4 / T17.1 in the §22 paper registry).

**Why this is in scope.**  Without `Constructive/Reals.lean`, the
mass-gap theorem T17.1 in Lean is the composition of three abstract
bundle inputs (`OSReconstruction μ_∞`, `OSAxiomBundle μ_∞`, plus the
Q′-rational pilot data).  The bundle inputs are *types*, not proofs;
the analytical content lives in the paper.  With
`Constructive/Reals.lean`, the σ̂_∞-positivity statement and the
cluster-to-gap statement can both consume a constructive `CReal`
value as their conclusion, so the composed mass-gap theorem becomes
a single end-to-end Lean statement about constructive objects rather
than a composition over opaque bundles.

**Deliverables.**
- `lean/YMGap/Constructive/Reals.lean` providing:
  - `CReal` as a Bishop-style regular Cauchy sequence in `Q′` with
    explicit modulus.
  - Embedding `CReal.ofQ' : Q' → CReal`.
  - Constants `CReal.zero`, `CReal.one`, and named constants
    `ε_canonical`, `ε_wilson` matching the Q′ pilot values.
  - Arithmetic: `CReal.neg`, `CReal.add`, `CReal.sub` with
    regularity proofs (multiplication deferred to a follow-on,
    `CReal.mul`, since it requires boundedness machinery and is
    not load-bearing for σ̂_∞).
  - Order: `CReal.le`, `CReal.lt`, with reflexivity and transitivity.
  - The load-bearing bridge `CReal.le_of_Q'_le_approx`: if every
    rational approximation satisfies `ε ≤ approx_n + 1/(n+1)` then
    `ofQ' ε ≤ x`.
  - The limit constructor `CReal.limit_of_decreasing_bounded` —
    builds a `CReal` from a monotone-decreasing Q′ sequence
    bounded below.
  - Application: `sigma_hat_inf_creal` (constructed via
    `limit_of_decreasing_bounded` from the UV pilot σ̂-trajectory),
    `sigma_hat_inf_positive_creal` (T13.1 at the CReal level).
- Updated `lean/YMGap/Continuum/SigmaHatLimit.lean` exposing
  `sigma_hat_inf_creal` alongside the existing Q′-framework theorem.
- Updated `lean/YMGap/Continuum/OSReconstruction.lean` exposing the
  mass-gap bound at the `CReal` level (type signature; the
  analytical proof remains paper-only).
- Updated `lean/YMGap/MassGap/SU2.lean` exposing
  `mass_gap_SU2_creal` returning a `CReal` mass bound rather than
  the abstract spectral-gap statement.
- Updated `lean/SORRY_LEDGER.md` recording any remaining paper-only
  bridges between `CReal` and the operator-spectral statements.
- Updated `docs/outline.md` Part B §22 theorem registry indicating
  T13.1, T16.5, T17.1 are now "Lean-formal statement at the CReal
  level" rather than "Lean type-signature against abstract bundles."

**Dependencies.** Milestones 6.4 (UV-direction trajectory),
7.1 (σ̂_∞ Q′ framework), 7.2 (continuum measure paper-only existence).

**Axiom-gate.**  Every load-bearing theorem in
`Constructive/Reals.lean` must pass `#print axioms` with `propext`
only.  `Quot.sound` may appear if a `Quotient`-based equality is
used for `CReal` equivalence, in which case the use must be
justified in the module docstring per AGENTS.md Rule 1.

**Open questions.**
1. Whether to expose multiplication `CReal.mul` in this module or
   defer to a follow-on Milestone 7.3-mul.  Multiplication of
   Cauchy sequences requires boundedness lemmas and a re-scaled
   modulus; not load-bearing for σ̂_∞.  Recommendation: defer,
   document the deferral, and add `mul` if Phase 10 needs it.
2. Whether to use `Quotient` (with `propext` + `Quot.sound`) for
   `CReal` equality, or to keep equality as `Setoid`-style
   "equivalent regular sequences" without quotienting.  The latter
   avoids `Quot.sound` but requires every downstream theorem to
   carry an explicit equivalence hypothesis.  Recommendation:
   `Setoid` form, since the downstream use is *inequality* not
   *equality*; equality on `CReal` is genuinely undecidable and we
   should not pretend otherwise.
3. Whether to extend the module with `CReal.sqrt` for the
   `m ≥ σ̂_∞^{1/2}` step.  The square root of a Cauchy sequence of
   nonneg rationals is itself a Cauchy sequence (via Newton iteration
   at the rational level); doable in the module's idiom but is
   non-trivial work.  Recommendation: not in this milestone; ship
   `CReal.sqrt` separately as Milestone 7.3-sqrt if needed for the
   m_0 upgrade.

**Estimated effort.** 600–1,200 lines of Lean for the focused
deliverable above; 2,000–3,000 if `mul`, `sqrt`, and the full
ordered-ring axioms are included.  The focused-deliverable form is
sufficient for T13.1, T16.5, and the mass-gap statement at CReal
level, which is the named scope of this milestone.

---

## Phase 8: Osterwalder–Schrader reconstruction

**Phase goal.** Verify the Osterwalder–Schrader axioms for the
continuum SU(2) Wilson measure `μ_∞` (Phase 7.2) and apply the
reconstruction theorem to obtain a Hilbert space with a self-adjoint
Hamiltonian, ready for the mass-gap analysis of Phase 9.

**Foundational references.** [Jorgensen1986AnalyticContinuation]
(Pac. J. Math. 125) on analytic continuation of local Lie-group
representations and its OS-positivity connection (PDF in
`docs/pdf_references/`). Klein–Landau prior work on OS positivity
cited within. The lattice-to-continuum OS-axiom-lift uses the
projective-limit construction of Phase 7.2.

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
Yang–Mills, mirroring the Clay Millennium problem statement of
[JaffeWitten2006] (PDF in `docs/pdf_references/`):

> "*Yang–Mills Existence and Mass Gap.* Prove that for any compact
> simple gauge group $G$, a non-trivial quantum Yang–Mills theory
> exists on $\mathbb{R}^4$ and has a mass gap $\Delta > 0$. Existence
> includes establishing axiomatic properties at least as strong as
> those cited in [Streater–Wightman, Osterwalder–Schrader]."

The Clay-statement definition of the mass gap is:

> "A quantum field theory has a mass gap $\Delta$ if $H$ has no
> spectrum in the interval $(0, \Delta)$ for some $\Delta > 0$. The
> supremum of such $\Delta$ is the mass $m$, and we require
> $m < \infty$."

Our Phase-9 target is the SU(2) instance of this: the continuum-limit
Hamiltonian `H_op` (Phase 8.2) has a spectral gap above the ground
state, `inf σ(H_op) \ {0} > 0`. Per the Phase-3 inductive-step
infrastructure, the project produces a CONSTRUCTIVE lower bound `m_0
≤ m`, not just an existence claim.

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

#### CI axiom-gate enforcement

The constructive law above is enforced in CI by a per-theorem
axiom-baseline audit:

- `scripts/lean_axiom_audit.py` parses `lake build` output and compares
  each theorem's `#print axioms` result against `lean/AXIOM_AUDIT.md`
  (the maintained baseline of permitted axioms per theorem).
- **Drift detection** (CI fails, exit 1): a tracked theorem acquires
  an axiom dependency NOT listed in the baseline (e.g. `Classical.choice`
  appears where only `propext` is permitted).
- **Improvement detection** (silent pass): a tracked theorem's axiom
  set shrinks (the proof became more constructive).
- **Strict mode** (`--strict`, exit 2): also flag new theorems not in
  the baseline and tracked theorems missing from the build.  Used as
  an informational warning in CI; the maintainer accepts new theorems
  by running `make lean-audit-update` and committing the manifest.

Makefile targets:
- `make lean-build`         — `lake build` in `lean/`.
- `make lean-audit`         — non-strict drift check.
- `make lean-audit-strict`  — also fail on new/missing theorems.
- `make lean-audit-update`  — regenerate the baseline.

GitHub Actions workflow: `.github/workflows/lean-audit.yml` runs
`make lean-build` + `make lean-audit` on every push/PR that touches
`lean/`, `scripts/lean_axiom_audit.py`, or the workflow itself.  The
strict mode is run informationally (`continue-on-error: true`) and
surfaces new/missing-theorem warnings without blocking the merge.

This converts the manuscript's Appendix B (Lean axiom-gate audit, per
`docs/outline.md` Part B §22) from a one-time snapshot to a
maintained guarantee: every PR-merge commit has a passing axiom-gate
audit, and the `lean/AXIOM_AUDIT.md` manifest is the auditable
reproducible record.

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

1. ~~**P3.2 large-field amplitude.** $\rho_{\mathrm{lf}}$ is derived from
   the SU(2) Casimir and the chosen convention; $K_{\mathrm{lf}}$ is
   still placeholder `1.0`.~~
   **CLOSED 2026-05-26**: $K_{\mathrm{lf}}$ is now derived via
   heat-kernel character-tail truncation + Brydges–Federbush cluster
   expansion in `computations/large_field_kp.py` (formula
   $K_{\mathrm{lf}} = q/(1-q)$ with $q = \mu_{\mathrm{plaq}} \cdot
   Z_t^{\mathrm{upper}}$).  At canonical $g = 0.30$:
   $K_{\mathrm{lf}} \approx 0.0156$; at Wilson $g = 0.50$:
   $K_{\mathrm{lf}} \approx 0.000393$.  The Q'-rational Lean
   algebraic-derivation closure
   (`Sheaf.SU2KP.K_lf_canonical_derivation`,
   `K_lf_wilson_derivation`) verifies the Brydges–Federbush
   convergence relation `q ≤ K_lf · (1 - q)` at the rounded Q' values.
   Remaining literature-shape fiducial: $\mu_{\mathrm{plaq}} = 16$
   (Seiler 1982 form, not directly verified against a primary source
   in the 2026-05-24 audit; rigorous BF-conservative fallback
   `MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e` is available and yields
   pilot closure at the canonical $g_0 = 0.30$ wire-in essentially
   unchanged).
2. ~~**P3.1 coefficient extraction.** The small-field spectral-gap
   coefficient $c_{\lambda}=1/2$ is fiducial pending direct extraction
   from the Bałaban estimates in the project's normalization.~~
   **CLOSED 2026-05-26**: $c_{\lambda}$ is now derived as the SU(2)
   Casimir gap $C_2(\tfrac12) = \tfrac34$, identifying the leading
   spectral-gap scale of the small-field activity with the same
   Casimir-driven decay rate that governs the buffer-shell bound
   (`heat_kernel.kappa_from_casimir`).  The previous value $\tfrac12$
   was a pilot-tolerance fiducial; the new value is project-consistent
   and Bałaban-literature-compatible.  Downstream impact at the
   canonical pilot $g_0 = 0.30$: $g_{\max}^{\mathrm{sf}}$ shifts from
   $0.40$ to $0.49$ (+23% wider convergent regime); $\eta_{\mathrm{tot}}$
   shrinks from $33/10000$ to $9/10000$; the constructive mass-gap
   lower bound tightens from $m_0 = 998/1000$ to $m_0 = 999/1000$.
   Lean-mirrored in `Sheaf.SU2KP.c_lambda := Q'.C2_oneHalf` with the
   algebraic-derivation theorem `rho_sf_canonical_derivation` reverified.
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

---

## Phase 11: Continuum frontier — the Tier-0 atom campaign

> **Status note (2026-07-03).** This phase supersedes the 2026-05-25
> "Suggested next milestone" note above as the current recommendation.
> Phases 0–10 delivered: a sorry-free, `Classical.*`-free `YMGap`
> library; the fixed-spacing Clay rubric line
> (`Rubric.ClayScorecard.clay_fixed_spacing_met`) genuinely proved; and
> the open continuum problem *machine-checked as an enumeration* —
> `Continuum.Tier0Scorecard` (Sub-wall A: (T′), (D1), (D2), (A2);
> Sub-wall B: `SpectralMarginInput` = `hlocalize` + `hbridge` + `hadd`;
> orthogonal: `CitedMinlosLift`), with `ClayTarget` additionally naming
> O(4) restoration, coupling-uniformity, gauge content, asymptotic
> freedom, and nontriviality. Phase 11 is the campaign against those
> atoms. Milestones are ordered by (leverage × tractability); 11.0–11.6
> are largely mechanizable with current machinery, 11.7–11.8 are the
> research core (the actual open mathematics), 11.9–11.12 are the
> Clay-shape completions. Milestones marked **[research]** must be
> prose-first (`formal/` + `notes/`) per AGENTS.md Rule 5: do not
> invent Lean witnesses ahead of the analysis.
>
> **Standing anti-pigeonhole rule for this phase.** Every milestone
> below names its *currently best-known route* in enough detail to
> start work, but the checkable predicate is the Lean type that must
> be inhabited (or the named hypothesis that must be discharged) — not
> the route. If a better route inhabits the same type, take it and
> record the deviation in the milestone's closure note.
>
> **Composition update (2026-07-03, from the external GPT review
> `docs/GPT/030726_YM_GPT_Review.md`).** Two structural findings are
> folded into this phase:
>
> 1. **There are TWO machine-checked frontier enumerations, not one.**
>    Alongside `Tier0Scorecard`'s eight atoms (the measure/RG side),
>    `Rubric/ReconstructionScorecardFinal.lean` names five open
>    operator/OS-side tokens: `OpenNode1FiniteSMargin` (finite-s
>    theta-floor saddle margin), `OpenTrueMargin`
>    (`UniformCouplingFromAF.TrueMarginRecursion` — the genuine
>    dimensionless `Δ_k = m_lat(a_k)/a_k`, DISTINCT from the proved
>    survival-product surrogate), `OpenPhysicalWilsonBridge`
>    (`WilsonSpectralBridge.CharacterDiagResolution`),
>    `OpenBoundedHamiltonian`
>    (`BoundedFunctionalCalculusResidual`, `e^{−H} = T`), and
>    `OpenContinuumMinlos`. These overlap the Tier-0 atoms (Minlos
>    verbatim; the `DeltaFrontierLedger` residual `bulkCtrl` is the
>    `hlocalize` content; `OpenTrueMargin` vs `UniformSpacingFloor`)
>    but are not identical — bridging or unifying them is now
>    Milestone 11.14, and 11.0's audit covers BOTH lists.
> 2. **The pinning principle.** Several rubric clauses are inhabitable
>    only because their statements are still weak enough to admit
>    surrogate/model witnesses (the survival-product floor inside
>    `ReconstructionProvedLine` is the confirmed example; existential
>    defect schedules in O(4) clauses are the pattern). Strengthening
>    the top-level target so that all fields are pinned to the SAME
>    physical objects (same `G`, same continuum measure, same
>    observable algebra, same Hamiltonian) — so that the only way to
>    inhabit it is to solve the problem — is now Milestone 11.13, and
>    surrogate-green clauses must be labeled `MET-surrogate` per the
>    Rule 9 update. Milestones 11.13–11.17 below carry the
>    composition; 11.13/11.14 are architecture-tier (schedule with
>    11.0), 11.15 gates the heavy 11.8 investment, 11.16 is
>    mechanizable-tier, 11.17 is statement-layer Clay coverage.

### Milestone 11.0 — Frontier re-audit and scorecard synchronization

**Status.** DONE (2026-07-03) — `scripts/frontier_status.py` + `make frontier-status` + `docs/frontier-status.md` (304 lines, OPEN-by-design ledger; `--lake`/`--stdout`/`--from-file` flags), walking the 7 frontier bundles.

**Goal.** A single generated document in which every open atom of
`Tier0Scorecard` / `ClayTarget` / `FourDExistence.ContinuumYMExistence`
is listed with (a) its Lean type, (b) its current best partial close
(module + declaration), (c) what field(s) remain genuinely open, and
(d) the axiom gate of the partial close — regenerated from the build,
not hand-maintained, and consistent with the module docstrings.

**Why first.** The docstrings already lag the code: `Tier0Scorecard`
lists (D2) as open while `SepLatticeZ4Close.SepLatticeZ4_witness`
inhabits it (soundly, non-tightly); (T′) is reduced by
`TreeGraphBoundProgress` to three named legs; `hbridge` has its wiring
lemma in `PinnedBridgeProgress`; `lean/README.md` reports 493 tracked
theorems while `AXIOM_AUDIT.md` tracks 3758. An agent or referee
reading only the scorecards would mis-plan. This milestone is cheap
and de-risks every subsequent one.

**Deliverables.**
- `scripts/frontier_status.py`: walks a declared list of frontier
  bundle types, queries the build (via `lake env lean` elaboration or
  parsing of `#print axioms` output) for inhabitants / partial closes,
  and emits `docs/frontier-status.md`.
- `docs/frontier-status.md` (generated): the per-atom table described
  in the goal, dated.
- Docstring updates to `Continuum/Tier0Scorecard.lean` (and any other
  scorecard whose OPEN list has drifted) so PROVED/OPEN sections match
  the code. Where an atom has a *sound but non-tight* inhabitant
  (D2's L¹ metric), the docstring must say exactly that.
- A `make frontier-status` target; wire into CI alongside
  `lean-audit`.

**Dependencies.** None.

**Open questions.** Whether the generator should also *fail* CI when a
frontier bundle acquires an inhabitant (the guard is scoped as
Milestone 12.2; this milestone may deliver it early if convenient).

**Composition update (2026-07-03).** Scope extended per the GPT-review
composition:
- The audit walks **both** enumerations — the eight Tier-0 atoms AND
  the five `ReconstructionScorecardFinal` tokens — plus the
  `DeltaFrontierLedger` residual (`bulkCtrl`), and records suspected
  cross-list identifications for 11.14 to prove or refute.
- Add an **unimported-file audit**: list every `.lean` under `YMGap/`
  absent from `YMGap.lean`, each either imported or annotated with the
  documented-exclusion rationale (`PolyAtlas`/`ModuliAlgebra` pattern).
  Verified 2026-07-03: 602 files vs 600 root imports, so the current
  delta is tiny — keep it that way. (The external review flagged a
  `PenroseDomPartition.lean` as unimported; that file exists in
  neither the live tree nor the zip snapshot — the real object is
  `PenroseDomInduction.lean`, which IS imported. The *general* check
  is still worth automating; the specific claim was wrong.)
- Add a **`noncomputable` ledger**: the 9 `noncomputable` declarations
  (currently in `NormExcitedDrift`, `DominantModeRecursion`,
  `UniformCouplingFromAF`) each get a one-line classification —
  constructive extraction behind a Σ projection / convenience pending
  computable replacement / non-load-bearing helper — in a short
  section of `AXIOM_AUDIT.md` or a sibling ledger, per the AGENTS.md
  Rule 1 addendum.
- Record which rubric clauses are **MET-surrogate** vs MET-physical
  (the survival-product uniform-coupling floor is the known instance),
  feeding 11.13/11.15.

---

### Milestone 11.1 — (D2) separation metric: tightening decision and discharge

**Status.** DONE (2026-07-03) — `notes/d2-metric-sufficiency.md`, verdict (i): the L¹ `z4Sep` witness SUFFICES for every wired Sub-wall A consumer (only `PinnedCluster.connected_spanning_size_ge`, via `dist_self`/`dist_adj_le`/`dist_triangle`; raw dist never evaluated). L∞ needed only if `clusterSpanSum_decay` is re-routed through spanning-length (latent `PhysicalPairSepSupply`, off every wired path).

**Goal.** The `SubWallA.d2Sep` slot is discharged by a metric whose
strength is *matched to what the downstream Ursell decay actually
consumes*, with the decision recorded. Checkable predicate: either
(i) a note + Lean comment establishing that the existing L¹
coordinate-sum `SepLatticeZ4_witness` suffices for every downstream
consumer in Sub-wall A (currently only
`PinnedCluster.connected_spanning_size_ge` via `dist_le_pathLen`), or
(ii) a new inhabitant `SepLatticeZ4_linf` built from the
per-coordinate L∞ metric `maxᵢ |vᵢ(p) − vᵢ(q)|` with the three
`SepLattice` axioms proved (the triangle inequality is a 4-way
`max`/`omega` case split, already sketched in
`SepLatticeZ4Close.lean`'s "honest scope" section).

**Deliverables.**
- `notes/d2-metric-sufficiency.md`: for each Sub-wall A consumer of
  `d2Sep.val`, which metric property it invokes; conclusion (i) or
  (ii).
- If (ii): `lean/YMGap/Continuum/SepLatticeZ4Linf.lean` with the L∞
  inhabitant, axiom-gated, plus a domination lemma `z4dist ≤ linfDist`
  relating the two.
- `Tier0Scorecard` docstring updated to mark (D2) CLOSED (sound) or
  CLOSED-tight accordingly.

**Dependencies.** 11.0.

**Open questions.** Whether the eventual (T′)/(D1) closures need
*directional* separation (non-collapsing along constant-sum
directions) — if yes, (ii) is forced; the note should pre-answer this
for the 11.2/11.3 authors.

---

### Milestone 11.2 — (T′) tree-graph inequality: close the three legs

**Status.** CURRENTLY IN PROGRESS (2026-07-03) — leg (A) `CubicEulerBound` PROVED (`Continuum/CubicEulerBound.lean`, (n+1)ⁿ≤3nⁿ, Nat Bernoulli, axiom-clean) → leg (A) DONE. Leg (C) `cayleyMax` PARTIAL (`Continuum/CayleyMaxBound.lean`): FINDING — the unconditional target is FALSE for multigraphs (treeCount = edge-SUBSET count; needs `SimpleEdges`), and deletion-contraction is INSUFFICIENT for Cayley; reduced to `CayleyCountBound`. Leg (C) FURTHER reduced (`CayleyPruferInjection.lean` → `CayleyInjection.lean`): cardinality half PROVED; `cayleyCountBound_of_memEqSpec` reduces the Prüfer LIST-injectivity to the strictly-weaker SET-membership form `PruferMemEqSpec` (via `sublists_eq_of_mem_iff`); the genuine leaf-determinacy content stays uninhabited. NOTE: off the mass-gap critical path (the `TreeGraphReduction` datum is itself uninhabited). Leg (P) `penroseDom` stays under `PenroseDomInduction.lean`.

**Goal.** `Ursell4DProgress.TreeGraphBound` is inhabited for the
pinned truncated-Ursell `phiT` — i.e. the per-cluster bound
`|φ^T(Y)| ≤ 3^{|Y|}` is a theorem, not a field. Per
`TreeGraphBoundProgress`, this decomposes into three named legs;
closing all three and composing is the milestone.

**The three legs (current best route).**
1. **(A) `CubicEulerBound`** — `(n+1)^n ≤ 3·n^n` over `Q'`/`Nat`
   (the `e < 3` bound). Elementary; candidate proofs: binomial
   expansion via the existing `Continuum/BinomialTheorem.lean`
   (`(1+1/n)^n = Σ C(n,k)/n^k ≤ Σ 1/k! ≤ 3` at the rational level),
   or direct strong induction. No new mathematics; this leg should
   close first and unblocks everything downstream already proved in
   `TreeGraphBoundProgress`.
2. **(C) `cayleyMax`** — spanning-tree count `≤ n^{n-2}`. Candidate
   constructive route: a Prüfer-sequence *encoding* (an injection
   from spanning trees of any graph on `n` labeled vertices into
   `Fin n ^ (n-2)` sequences, via the complete-graph maximizer) —
   injectivity gives the count bound without needing the full Cayley
   bijection. Moderate combinatorics, fully finitary.
3. **(P) `penroseDom`** — the Penrose / BKAR forest-root sign
   domination `n!·|φ^T(Y)| ≤ #spanningTrees(adjGraph Y)`. **This is
   the sole genuinely new mathematics in (T′)** and is **[research]**:
   write the Penrose-resummation proof in
   `formal/tree-graph-bound.tex` first (Poghosyan–Ueltschi 2009 /
   Friedli–Velenik §5.4 as the model), identify the finitary
   induction (partition-scheme over rooted forests), then mechanize.

**Deliverables.**
- Lean: the three legs as theorems; the composite
  `treeGraphBound_witness : TreeGraphBound d2 w4 gr` (over the 11.1
  metric); axiom gates recorded in `AXIOM_AUDIT.md`.
- `formal/tree-graph-bound.tex` (leg P prose proof).
- Scorecard update: Sub-wall A drops from 4 atoms to 3 (then to 2 with
  11.3).

**Dependencies.** 11.0; 11.1 (for the metric the bound is phrased
over). Legs (A) and (C) are independent of each other and of (P) —
parallelize.

**Open questions.** Whether `phiT` should be *defined* in Lean (the
truncated Ursell coefficient as a finite signed sum over connected
graphs) as part of this milestone or pinned by interface — defining it
is strongly preferred (it is a finite rational object) and is what
makes leg (P) a theorem rather than a model identification; budget for
the combinatorial infrastructure (connected-graph enumeration over a
finite polymer) accordingly.

---

### Milestone 11.3 — (D1) Mayer–Ursell bridge decomposition

**Status.** CURRENTLY IN PROGRESS (2026-07-03, degeneracy FIXED) — `Continuum/MayerUrsellZ4Restated.lean` `MayerUrsellIdentity_z4_v2` normalizes the d=0 diagonal against the positive vacuum activity (`kpTerm…0=1`) instead of the vanishing span (non-degeneracy certificate `diagModel`, w0=1/2, weight>0); `decompose_v2` PROVED, chains to `corr d ≤ 2·(15/32)^d`. The reduction now bottoms out CLEANLY on the SHARED Sub-wall A atoms (T') tree-graph + (D2) SepLattice — no forced-zero collapse. (Superseded the degenerate v1 finding `mu_z4_total_weight_le_zero`.)

**Update (2026-07-09).** The 2026-07-08 campaign (commits `f05e270`, `d8c58b5`, `4c7c114`) discharged (D1) AS TYPED but QUALIFIED: the KP-assembly half is PROVED (`physical_to_v2`), both phantom traps are machine-proved and avoided, and `expansion_sep` is inhabited by the genuine strictly-positive `reconTransfer w4` — but that model is SINGLE-LINE, so the free-`model` typing leaves the loopy multi-plaquette physics uncaptured (the systematic under-constraint finding, `69f2e0f`). The honest residual is now the PINNED LOOPY form — `PenroseUrsellDatumG.penrose_ursell` with `offCorr` a genuine finite-volume multi-plaquette correlator — tracked as **Milestone 13.1** (in progress); this milestone's own statement work is complete.

**Goal.** `Ursell4DProgress.BridgeDecomposition.decompose` is a
theorem over the closed 4D cluster count `z4ClusterCountBound`: the
off-diagonal connected correlator at separation `d` is dominated by
its bridge-Ursell tail sum. Checkable predicate: an inhabitant
`bridgeDecomposition_witness : BridgeDecomposition (z4ClusterCountBound p) w4 gr`
with no open fields.

**Current best route.** The absolute connecting-cluster expansion of
Friedli–Velenik Ch. 5 (the same source already tracked for
`KPIncrementData`): every connecting cluster contributing at
separation `d` contains a bridge of length `≥ d`; resum by bridge
length using the geometric machinery already in
`Constructive/GeometricTail.lean` and the KP telescoping pattern of
`Continuum/KPIncrement.lean`. This is bookkeeping-heavy but standard;
the honest hard part is the same cluster-enumeration infrastructure as
11.2's `phiT`, so **share that infrastructure** (build it once, in one
module, consumed by both).

**Deliverables.**
- The shared finite-cluster enumeration module (if 11.2 hasn't already
  landed it).
- Lean: `bridgeDecomposition_witness`, axiom-gated.
- `notes/mayer-bridge-decomposition.md` recording the exact resummation
  and where it deviates (if anywhere) from Friedli–Velenik.

**Dependencies.** 11.0; shares infrastructure with 11.2 but neither
blocks the other's *statement* work.

**Open questions.** Whether the `tailLen` schedule carried by the
structure is the right one for the eventual Sub-wall A assembly, or
whether it should be generalized to any summable schedule (prefer
generalizing only if the assembly demands it).

---

### Milestone 11.4 — (A2) the pentagon: exact rational 6j program **[research-adjacent]**

**Status.** DONE (2026-07-03, pilot + kernel) — `computations/wigner_6j.py` (+tests, 12 pass): exact-rational Racah 6j; pentagon & orthogonality sweeps exact (`Fraction(0)`); P=1/4 pin matches Lean. `Continuum/SixJKernel.lean`: `racahKernelCore : PentagonNumericCore` — a FAITHFUL varying rational dim·6j² kernel (P=0 off-triangle, P=1/4 at the smallest tetra) + a genuine orthogonality sum rule (by `decide`), axiom-clean. KEY FINDING: the signed 6j / Biedenharn–Elliott associator is IRRATIONAL (√-triangle coeffs) → B–E is NOT Q'-representable; the SQUARED kernel satisfies ORTHOGONALITY, not B–E. So full `SixJPentagon` via a rational B–E is impossible — the honest target is the orthogonality identity, now REDUCED (`Continuum/RacahOrthogonalityGeneral.lean`): the off-triangle half PROVED for ALL labels, the on-triangle half → the SOLE residual `DiagonalSixJNormalization` (Σ_x (2x+1)(2f+1){6j}²=1, the fractional 6j orthonormality — needs a 3j/Clebsch–Gordan layer, not in-tree).

**Goal.** `Tier0Scorecard.SixJPentagon` is inhabited: a rational
dim-absorbed 6j-square kernel that provably closes the guarded
Biedenharn–Elliott cubic. Checkable predicate:
`sixJPentagon_witness : SixJPentagon` with `pentagon` a theorem.

**Current best route** (respecting the `PentagonRelation.lean`
three-level analysis — the permutation surrogate `racahRP` is proved
*insufficient*, so a faithful kernel is required):
1. Implement the SU(2) Wigner 6j via the Racah single-sum formula in
   exact arithmetic. Track the known rationality structure
   explicitly: the triangle coefficients contribute square roots, so
   represent the *signed square* `(2e+1)(2f+1)·{6j}²` (rational) plus
   the sign function as separate data, exactly as `PentagonRelation`
   already frames the `Q'`-legal statement.
2. Gate with computation: verify the pentagon identity by `decide` /
   kernel evaluation on a bounded rep window (all reps `< D` for small
   `D` — e.g. all spins ≤ 2). This is the cheap falsifier for the
   chosen index wiring (the file itself warns the wiring is
   "structural shape, not the textbook assignment" — the bounded check
   settles whether the shape is the true identity or needs
   re-indexing; **budget for one re-indexing round**).
3. Prove the general identity. Candidate: recoupling associativity —
   both sides of the pentagon compute the same change-of-basis between
   two parenthesizations of a 4-fold tensor product; at the
   `Q'`-rational squared-kernel level this becomes a finite sum
   identity per rep tuple, provable by induction on total spin, or by
   the hypergeometric (Racah polynomial) contiguity relations.
4. Inhabit `SixJPentagon` and thread `pentagon_to_racah` domination.

**Deliverables.**
- `computations/wigner_6j.py`: exact-rational 6j (squared) + sign,
  with the pentagon verified numerically/symbolically over a sweep —
  this is the Rule-5 pilot the Lean work mirrors.
- Lean: the rational kernel definition; the bounded-window `decide`
  theorem; the general pentagon theorem; the witness.
- `formal/6j-pentagon.tex` if step 3 needs a prose proof first.

**Dependencies.** 11.0. Independent of 11.1–11.3 — parallel track.

**Open questions.** Whether the guarded form (`< D` largeness bound)
is what the eventual Sub-wall A assembly consumes, or whether an
unguarded identity is needed; whether SU(2)-specific 6j suffices for
the Clay-general assembly or the milestone should leave a group
parameter (default: SU(2) now, generalize when 11.12's interfaces
demand it).

---

### Milestone 11.5 — Sub-wall B: discharge `hadd` (the units dictionary)

**Status.** DONE (2026-07-03) — `Continuum/HaddDischarge.lean`: `spectralMarginInput_of_edgeLocalization` installs the PROVED `hadd` (`hadd_is_installed` by rfl) + `continuum_floor_pos_of_edgeLocalization` (0<physGapMin end-to-end). Sub-wall B drops 3→2 atoms {hbridge, hlocalize}; hadd is now a theorem of the strictly-sharper {hEdge, hFR, bulk_shift}. Axiom-clean, guard-safe.

**Goal.** The `hadd` field of
`AsymptoticSpectralLoc.SpectralMarginInput` — the located-second-
eigenvalue ↔ physical-margin dictionary — is discharged by a theorem,
reducing Sub-wall B from three open atoms to two. Checkable predicate:
a constructor `spectralMarginInput_of_… ` that no longer takes `hadd`
as a field but *proves* it from the pinning already mechanized in
`PinnedBridgeProgress` (`shift_k := divPos ((L k).shift 1) a`,
`floorRate_k = heatKernelMargin w_k = 1 − w_k³`).

**Current best route.** This is a translation lemma between two
representations the library already owns (`LocatedSpectralGap.gapMargin`
on one side, the `Stage2ConvergesToMargin` physical-margin family on
the other), with the `1/a` units factor handled exactly as
`hbridge_pinned_of_edge` handles it. Expected to be `Q'` algebra plus
the existing `margin_cube_ge` factorization — no new analysis.

**Deliverables.**
- Lean: the discharging constructor + `#print axioms` gate; scorecard
  and `SORRY_LEDGER.md`-style named-hypothesis bookkeeping updated.
- One-paragraph note in `docs/frontier-status.md` regeneration.

**Dependencies.** 11.0.

**Open questions.** Whether the dictionary is cleanest stated at fixed
`k` (per-scale) or uniformly; take whichever the Stage-2 collapse
consumes without re-plumbing.

---

### Milestone 11.6 — Sub-wall B: discharge `hbridge` (pinned shift control)

**Status.** CURRENTLY IN PROGRESS (2026-07-03) — `Continuum/HbridgeInputs.lean`: (b) hLin CLOSES as an owned schedule choice (`pinnedDelta := bmConst·(1−w_k)` makes the linear-control field reflexive; `HbridgeScheduleInput.hbridge` is then a THEOREM over the proved `bondMovingDeltaRen_quadratic`). Whole `hbridge` → SOLE residual (a) `hId` (node ① bulk_shift). FINDING (a theorem, not a hope): the summable-tower compatibility holds ONLY for a non-AF super-linear margin — the AF-marginal harmonic `1−w_k∼1/k` diverges (`lossSum_pinnedDelta_eqv`/`pinnedDelta_summable_of_marginSum`).

**Goal.** The `hbridge` field is discharged for the physical
`g_k ≠ 1` trajectory. `PinnedBridgeProgress` already delivers the
wiring lemma `edgeShift_le_gradedDefect` and the `1/a` lift
`hbridge_pinned_of_edge`; what remains is supplying its two inputs as
theorems rather than hypotheses: (a) the **model identification**
`s ≤ bondMovingDeltaRen N p w` (the located edge shift is controlled
by the quadratic bond-moving budget), and (b) the **near-continuum
linear control** `bmConst p·(1 − w) ≤ δ` on the operating schedule.

**Checkable predicate.** A constructor producing `hbridge` from the
spacing schedule and the already-proved
`BondMovingQuadratic.bondMovingDeltaRen_quadratic`, with (a) and (b)
either proved or reduced to *strictly smaller* named inputs that are
logged per AGENTS.md Rule 6 and enumerated in the regenerated
scorecard.

**Deliverables.**
- Lean: the constructor; if (a) remains partially open, its residue
  must be a sharper named field (never a regression to the opaque
  `hbridge`).
- `notes/hbridge-model-identification.md`: exactly what (a) asserts
  physically and its literature anchor.

**Dependencies.** 11.0, 11.5 (shares the pinning).

**Open questions.** Whether (b) is a *choice* (pick the schedule so
the linear control holds — likely, since `SpacingSchedule` is
project-owned data) or a constraint to verify against the AF
calibration files (`AFRateCalibration` etc.); prefer the choice route
if it doesn't distort the AF matching.

---

### Milestone 11.7 — Sub-wall B: `hlocalize` (Core B local-CLT) **[research]**

**Status.** CURRENTLY IN PROGRESS (2026-07-03, DEDICATED TRANCHE done) — statement layer `Continuum/FusionKernelStatement.lean` (fusionKernelNorm/fusionEig + SaddleLogForm/SaddleLocalCLT → bulkCtrl). Tranche (pilot+prose+Lean+memo): `computations/core_b_pilot.py` (+16 tests) — the η_p·C₂² estimate side is SATISFIABLE (η<1/12 in EVERY (w,p) cell, worst 0.00246, 34× margin) and the Tier-0 mirror validates exactly (Δ²C₄=2, d2x max 0.620<1, pfmom_split rel-err 1.9e-17). **UNIFICATION** (`Continuum/FusionSaddleReduction.lean`): `bulkShiftBound_p2_of_tier0` provably reduces the p=2 fusion saddle residual to the Tier-0 `XMeanSecondDiffLeOne` (d2x≤1) + 2 named bridges (`FusionAdditiveBridge`, `CurvatureToShift`) — both Core-B faces now bottom out on ONE residual. `formal/core-b-local-clt.tex` (gap-flagged, non-circular two-halves corrected) + `docs/core-b-decision-memo.md`. ⚠ BUG FOUND by the pilot: the LITERAL `SaddleLocalCLT.bulkShiftBound` (bare `eigA=w^{c4·s}`) is FALSE for all p≥2 (35/35 cells) — must be RE-BASED to `w_eff=exp(−A_p)` (the estimate side is unaffected); follow-up fix in `FusionKernelStatement`. DECISION: iterate prose + mechanize the p=2 face; NO route change. **4-ROUTE ATTACK (2026-07-04)** — all four converge on the SAME curvature wall, maximally sharpening Core B: (1) `Continuum/FusionShiftMonotone.lean` — the telescoping collapse of the infinite {shift_p}_{p≥2} family onto the SINGLE p=2 base is PROVED (axiom-clean), reducing all p≥2 to ONE single-step monotonicity atom `FusionShiftStep` (shift(p+1)≤shift p) [NOT from Karlin — the fusion product is truncated-CG, not additive]; (2) `Continuum/MeanComplementClose.lean` — the naive Var≥0 closure is REFUTED; the EXACT Casimir ledger Δ²(4⟨x⟩+⟨D²⟩)=2 is PROVED, recasting the p=2 `d2x≤1` (ring-level ↔) onto the single cleanest residual `TwoPointTieSubleading` (Δ²⟨D²⟩ ≥ −2, corner-tight = the sub-leading two-point-tie local-CLT / Tate–Zelditch constant); (3) `Continuum/DiscreteLaplaceSaddle.lean` — the leading −A·C₂ Gaussian term is PROVED to have exactly curvature Δ²C₄=2 (`leadingExponent_secondDiff`), the C₂² remainder = `EtaRemainderResidual` on the SAME DShiftCovResidual wall; (4) `Continuum/RebasedBulkShift.lean` — the p≥2 statement bug is FIXED (re-based rate `rateP w_eff`, p=1 anchor inhabited), collapsing the p≥2 obligation to the single exp-Lipschitz `ExpShiftBridge` (⚠ the wave-4 `FusionKernelStatement.SaddleLocalCLT.bulkShiftBound` is SUPERSEDED — known-false for p≥2; use `RebasedLocalCLT`). NET: Core B = {p=2 variance floor Δ²⟨D²⟩≥−2 (corner-tight) + single-step p-monotonicity + exp re-basing}, with the Gaussian leading term proved — an infinite-family estimate reduced to one finite corner-tight variance floor + one monotonicity step. Still OPEN (both residuals are the genuine wall).

**Goal (long-horizon; this milestone is the *first tranche*).** The
`sl.hlocalize` field — the p ≥ 2 SU(2)-fusion local-CLT spectral
localization — discharged. First-tranche checkable predicate: a
complete prose proof attempt in `formal/core-b-local-clt.tex` for the
**hierarchical model**, with every estimate carrying explicit
constants, plus a `computations/` pilot validating the constants
numerically over the operating window. Lean mechanization is *not* in
the first tranche (Rule 5: do not outrun the analysis).

**Current best route.** The `LocalCLTSteepestDescent` /
`FusionLogConcave` / `FusionCoreInduction` modules stake out the
intended structure: log-concavity of the fusion weights + a
steepest-descent local CLT gives the localization of the second
eigenvalue. The hierarchical model removes the geometry and isolates
the fusion analysis — exactly the setting where
`HierarchicalGap`/`TreeFixedSpacingGap` already live.

**Deliverables (first tranche).**
- `formal/core-b-local-clt.tex`: the hierarchical-model proof attempt,
  gap-flagged where incomplete.
- `computations/core_b_pilot.py` + tests: constants, window sweep,
  failure boundary.
- A decision memo: mechanize now / iterate prose / route change.

**Dependencies.** 11.5, 11.6 (so the localization statement lands in
its final consumable form). Parallel with 11.8.

**Open questions.** Everything — this is the open mathematics. The
milestone deliberately does not fix the proof technique; it fixes only
the *statement* (the existing Lean field) and the honesty protocol.

**Composition update (2026-07-03).** The GPT review supplies a
concrete lemma ladder for the first tranche, and the
`DeltaFrontierLedger` chain pins the target object; both are adopted:
- **Target identification.** The `hlocalize` content is the
  vacuum-normalized bulk eigenvalue-shift control `bulkCtrl`
  (`SpectralLocalizationCrux.SpectralLocalization`, `bulk_shift ≤
  1/12`), trivially inhabited at `p = 1`, open for `p ≥ 2` — the
  fusion local-CLT is the route to it, and the prose campaign should
  target exactly that field's statement.
- **Lemma ladder** (statement-level Lean may land early; proofs follow
  the prose per Rule 5):
  1. the vacuum-normalized p-fold fusion kernel
     `K_{w,p}(s) = [χ_s](K_w^{*p}) / [χ_0](K_w^{*p})` as a `Q'`-level
     definition;
  2. log-concavity / total positivity of the fusion coefficients
     (extending `FusionLogConcave`/`SelfFusionLogConcave`);
  3. the saddle / local-CLT estimate **with explicit rational error**,
     `log K_{w,p}(s) = −A_p(w)·C₂(s) + R_p(s,w)`,
     `|R_p(s,w)| ≤ η_p(w)·C₂(s)²`, moduli as data (Rule 8.3);
  4. wiring into the existing `DeltaToBlockPower` / `bulkCtrl`
     interface so the estimate discharges the ledger residual, not a
     parallel statement.
- The hierarchical-model prose proof of 3. remains the research heart;
  1., 2., and the statement of 3.–4. are first-tranche deliverables
  alongside the prose.
- `OpenNode1FiniteSMargin` (the `AcNReserveAnalytic.FiniteSMargin`
  steepest-descent remainder) is the same saddle-analysis family;
  assign it to this campaign's second tranche unless 11.14's bridge
  work shows it discharges from the same estimate.

---

### Milestone 11.8 — `UniformSpacingFloor`: hierarchical-model closure **[research]**

**Status.** CURRENTLY IN PROGRESS (2026-07-03, STATEMENT LAYER done) — `Continuum/CurvatureFloorStatement.lean`: `toModeEnergyFloor` (UniformCurvatureBound ⟹ ModeEnergyFloor via `BakryEmery.eigenvalue_ge_of_CD`) + `curvatureFloor : CurvatureFloorInput → QFloor` — a SECOND route to `UniformSpacingFloor`, interchangeable with the DefectGapRecursion route. Reduced to the SOLE residual `UniformCurvatureBound.uniform_CD` (one curvature constant K>0 with Bakry–Émery CD(K) at every spacing — the Bałaban/SZZ interacting estimate, the research core).

**Goal.** Inhabit `UnifiedContinuumFloor.UniformSpacingFloor` — the
single scalar all three continuum routes converge on
(`ContinuumFrontierScorecard.all_routes_converge_on_uniform_floor`) —
for the **hierarchical** Yang–Mills model, end to end, constructively.
This is the first point at which the project would produce *new closed
physics* rather than a sharper enumeration, and a publishable result
independent of full 4D.

**Checkable predicate.** A Lean term
`hierarchicalUniformFloor : UniformSpacingFloor …` (specialized to the
hierarchical tower) with axiom gate `[propext]`/`[propext, Quot.sound]`,
plus the composed positive continuum mass via
`unified_continuum_gap`, for an explicit rational floor.

**Current best route.** The Bakry–Émery curvature route
(`BakryEmeryGap`, `UniformCurvatureBound`, `ModeEnergyFloor`): a
curvature lower bound uniform along the hierarchical RG flow yields
the per-scale mode-energy floor directly. Fallback route: the direct
defect-gap recursion (`DefectGapRecursionProgress` +
`Stage2ConvergesToMargin`) fed by 11.7's hierarchical local CLT.
Pursue curvature first (fewer moving parts at fixed geometry); keep
both statements against the same `UniformSpacingFloor` type so the
routes stay interchangeable.

**Deliverables.**
- `formal/hierarchical-uniform-floor.tex` (prose first).
- `computations/hierarchical_floor.py`: the explicit floor value and
  its stability under the fiducial envelope (reuse the D-tornado
  machinery).
- Lean: the inhabitant + composition theorems, once prose closes.

**Dependencies.** 11.7 first tranche informs but does not block the
curvature route. 11.5/11.6 required for the OS-reconstruction route's
consumption only.

**Open questions.** Whether the hierarchical floor transfers any
quantitative content to genuine ℤ⁴ (expected: technique and
interfaces transfer; constants do not). The milestone's value stands
either way.

**Composition update (2026-07-03) — target-adequacy gate.** Before
heavy investment here, complete Milestone 11.15's reconciliation:
the GPT review argues (and `ReconstructionScorecardFinal` confirms a
surrogate-vs-physical split exists) that a floor interface can be
inhabitable by survival-product/model data while the Clay-relevant
quantity is the dimensionless physical margin `Δ_k = m_lat(a_k)/a_k`.
The 11.15 adequacy lemma (`TrueMarginRecursionPhysical →
UniformSpacingFloor`, or the retargeting if it fails) decides whether
this milestone's checkable predicate stays `UniformSpacingFloor` or
moves to the pinned physical margin. Do not close this milestone
against a floor the adequacy lemma has shown to be surrogate-weak.

---

### Milestone 11.9 — Continuum measure: the Minlos decision (Rule 4)

**Status.** DONE (2026-07-03, route i) — `lean/YMGap/Classical/MinlosQuarantine.lean` (interface-only re-export of `CitedMinlosLift`, AXIOM-CLEAN — no raw axiom, deliberately uninhabited) + first `lean/CLASSICAL_LEDGER.md` entry + `docs/continuum-measure-attack-surface.md` §status note.

**Goal.** The `CitedMinlosLift` atom is resolved by an explicit,
logged decision — currently `CLASSICAL_LEDGER.md` has **zero entries**
while a cited-classical input sits on the critical path, which
understates the chain's classical content. Checkable predicate: one of
(i) **quarantine route** — a module under `lean/YMGap/Classical/`
carrying the Minlos/Kolmogorov σ-additive extension as a
`CLASSICAL INPUT:`-docstringed axiom-or-import, re-exported through a
constructive interface, with the first entry in `CLASSICAL_LEDGER.md`,
and the Clay-facing chain re-verified against it; or (ii)
**constructive route** — `PartitionPos.BishopFunctional` extended to a
Daniell/Bishop–Cheng integral on the projective limit (the S2–S6
stages built most of this scaffolding), making the measure object
fully constructive and retiring `CitedMinlosLift`.

**Recommendation (non-binding).** Do (i) now — it is a bookkeeping
milestone that makes the Clay-facing chain honest and unconditional-
modulo-analysis, since Clay does not require constructivity — and keep
(ii) as the constructive upgrade with its own later milestone if the
Bishop route proves tractable.

**Deliverables.** Per the chosen route: the Classical/ module + ledger
entry + re-export, or the Daniell extension module; either way an
updated `docs/continuum-measure-attack-surface.md` §status.

**Dependencies.** 11.0. Independent of 11.1–11.8.

**Open questions.** For (ii): whether countable additivity in the
Bishop sense suffices for the OS-reconstruction consumers or whether a
full profinite-limit integration theory is needed — scope this in the
attack-surface doc before committing.

**Composition update (2026-07-03).** The GPT review concretizes route
(ii) as a **pinned tightness/projective tower** — adopt it as the
named shape of the constructive route: a structure over the physical
volume/spacing tower carrying `finiteMeasures`, projective
`consistency`, an **explicit tightness modulus**, **explicit
cylinder-convergence moduli**, and survival fields for reflection
positivity, gauge invariance, and (interfacing 11.10) O(4)
restoration — followed by a theorem
`continuumMeasure_from_tightTower : TightTower → Σ μ, OSMeasureProperties μ`.
Constructive corrections to the sketch: all moduli are `Type`-level
data (Rule 8.3), the conclusion is `Σ` not `∃` (Rule 2), and
"summable" claims carry rate data. Under this framing, route (i)'s
quarantined Minlos becomes the *classical comparison point* the tower
theorem eventually retires — which is exactly Rule 4's intended
lifecycle. The recommendation stands: quarantine now (honest ledger),
build the tower as the replacement path, and let 11.14's FrontierDAG
carry `continuumMinlos` as one node with both routes recorded against
it.

---

### Milestone 11.10 — O(4) restoration: from bare Prop to reduction-with-named-input

**Status.** DONE (2026-07-03, statement-layer reduction) — `Continuum/O4RestorationReduction.lean`: `o4_restoration_of_input` fires BOTH OS1 conjuncts (H₄ ∧ O(4)) from ONE pinned `O4RestorationInput`; H₄ proved from `ObsHom`s; non-vacuity capstone `isOS1Full_concrete` (concrete SU(2) heat-kernel `StrongO4Restoration` + isotropic `prodCharFunc` under `rot4`). Residual out-of-scope (11.8-class): the interacting `anisoDefect` AF decay for general ρ (pinned ρ=½ here).

**Goal.** `RubricO4Restoration` / `os1_o4_restoration` moves from a
bare uninhabited `Prop` to the project's standard
reduction-with-named-hypothesis shape (the pattern that worked for
`eta_dominated`): the H₄ (hypercubic) invariance at fixed spacing
**proved** from the lattice symmetry `ObsHom`s (the
`Spin4`/`Spin4Reflection`/`O4RestorationH4` groundwork), composed with
a **single named analytic input** — the decay of the
symmetry-breaking (irrelevant-operator) contributions along the
continuum limit, Magnen–Rivasseau–Sénéor-class — such that
`os1_o4_restoration` is a theorem *given* that one field.

**Checkable predicate.** A structure `O4RestorationInput` with the
irrelevant-decay field as `Type`-level data, and a theorem
`o4_restoration_of_input : O4RestorationInput … → IsOS1Full …`, both
axiom-gated; H₄ invariance itself carried as a proved theorem, not a
field.

**Deliverables.** The Lean module; `notes/o4-restoration-reduction.md`
stating precisely what the named input asserts and its literature
anchor; scorecard update.

**Dependencies.** 11.0. The named input's *discharge* is downstream of
11.8-class uniform control — out of scope here; this milestone is the
reduction only.

**Open questions.** The right formulation of "irrelevant decay"
constructively (a modulus on the H₄-to-O(4) defect of the Schwinger
moments is the leading candidate; leave room for a correlator-level
alternative).

**Composition update (2026-07-03) — pin the anisotropy.** The GPT
review sharpens the named-input requirement: the decay field must not
be an *existential defect schedule* (which weak witnesses can satisfy
vacuously). Adopt its pinning: the structure carries an
`anisotropy : Nat → Q'` together with a field asserting it is
**extracted from the physical Wilson action / transfer tower** (an
equation to a named extraction function, not a free choice), a
geometric decay bound `anisotropy k ≤ C·ρ^k` with `(C, ρ)` as data,
and the O(4)-invariant-limit conclusion phrased against the SAME
continuum measure as 11.13's pinned target. Note the repo already has
the non-posited pattern to imitate:
`O4BetaSign.o4_restored_of_tauModel` fires from the reciprocal AF
trajectory with no posited `betaDrop` — the milestone extends that
discipline from the β-coefficient to the full restoration input.

---

### Milestone 11.11 — OS reconstruction: construct the generator

**Status.** DONE (2026-07-03, stages a+b) — stage (a) `Continuum/BoundedHamiltonianFiniteVol.lean` (`FiniteVolumeBoundedH`, spectrum_nonneg/vacuum_zero/Δ_pos/selfAdjoint closed; floor branch on the pre-existing `YOfMonotone`/`ArtanhMonotoneWindow`). stage (b) `Continuum/CompletionGenerator.lean`: `builtSpectralGapData` over the ACTUAL Wilson completion `completeGnsHilbert` — `genGap` CONSTRUCTED from built objects (not free params); physical CReal `Δ=−log sep` carried alongside the rational `genGap` surrogate (the Q'/CReal boundary residual). Retires `OpenBoundedHamiltonian` at fixed volume.

**Goal.** The time-translation generator (Hamiltonian) on the
constructive complete GNS Hilbert space
(`WilsonGNSData.completeGnsHilbert`) is **constructed**, so
`OSReconstructedGap.genGap` is consumed from a built operator rather
than carried as interface data, and the fixed-spacing located transfer
gap is transported through the completion.

**Checkable predicate.** A definition producing, from the
finite-volume Wilson transfer data, a densely-defined nonnegative
self-adjoint-in-the-constructive-sense generator on
`completeGnsHilbert` (via the existing
`SelfAdjointHamiltonian`/`GNSHamiltonian`/`GNSDynamics` scaffolding),
together with a theorem that its per-scale spectral gap equals (or
dominates) the `LocatedSpectralGap` margin — making
`reconstructed_gap_ge_uniform_floor` consume a constructed object.

**Deliverables.** The Lean construction + transport theorem, axiom
gates; an update to the `Continuum/` README-status noting which
interface fields of `OSReconstruction` are now content-bearing.

**Dependencies.** 11.0; independent of Sub-walls A/B; strengthens the
consumer side of 11.8.

**Open questions.** Constructive self-adjointness formulation (located
spectrum vs. semigroup-generator): prefer whichever the existing
`BoundedTransferCalculus`/`ContinuousFunctionalCalculusForm` modules
already support; do not build a general constructive spectral theorem
if the compact-transfer special case suffices.

**Composition update (2026-07-03) — stage it, and name the token.**
This milestone is the discharge path for the reconstruction frontier's
`OpenBoundedHamiltonian` token (`BoundedFunctionalCalculusResidual`),
and the GPT review's staging is adopted:
- **Stage (a) — finite volume, bounded.** Construct the bounded
  self-adjoint additive `H` with `e^{−H} = T` for the finite-volume
  transfer operator, via the constructive spectral-mapping step
  `λ(T) ≤ μ < 1 ⇒ −log λ(T) ≥ −log μ > 0` (the `CRealLog`
  machinery exists; the located-gap transport is `Q'`/`CReal`
  algebra). Deliver `spectrum_nonneg`, `vacuum_zero`, and the
  `NoSpectrumIn H 0 Δ` gap clause as data-carrying fields.
- **Stage (b) — the completion generator.** Only after (a): transport
  through `completeGnsHilbert` as originally scoped, so
  `reconstructed_gap_ge_uniform_floor` consumes a constructed object.
Stage (a) alone retires `OpenBoundedHamiltonian` at fixed volume and
is the tractable 80% of the operator-theoretic node the scorecard
calls "the single irreducibly hard" one.

---

### Milestone 11.12 — All compact simple groups: realize the per-group data

**Status.** DONE (2026-07-03, faithfulness + per-type machinery; physical η = shared residual) — item 1 `RG/WeylDimGeneralData.lean` (crude WeylDimData, all 9 types). items 2–5 `MassGap/AllSimpleTypes.lean` (new leaf, axiom-clean): `admissible_of_cartanType` — FAITHFULNESS: every `CartanType` at a genuine-simple rank yields `AdmissibleSimpleGroup (repDataOf T)` via the PROVEN per-type `CasimirData` gap/h∨ floors (minimized only at A₁=SU(2)); `repDataOf : CartanType → RepData` carries the real per-type quadratic Casimirs; `uniformBudgetWitness_of_cartanType` (per-type `UniformBudgetWitness` via `uniformBudgetWitness_of_characterTail`, strict-monotone 13/313<1/2 regime); `mass_gap_of_cartanType` + per-type `mass_gap_A/B/C/D/G2/F4/E6/E7/E8` + `mass_gap_G2_via_weylData` (through `ofWeylData`), all conditional on the SAME OS interface as `mass_gap_SU3`. HONEST SCOPE: the faithfulness layer is genuine + type-specific (all ranks + all 5 exceptionals); the budget/η layer uses an admissible REPRESENTATIVE operating point (η_max = SU(3)'s proven value), so the group's OWN physical heat-kernel η — esp. the G₂/F₄ short-root Killing-form normalization — stays the pre-existing SHARED `UniformBudget.eta_dominated` residual (the same gate SU(3) is under). NET: R1 (group dependence) is realized for ALL compact simple types at SU(3)'s standing.

**Goal.** The Clay quantifier "any compact simple gauge group G" is
covered at the lattice layer: the uniform reduction
(`mass_gap_simple_group` via `uniformBudgetWitness_of_characterTail`)
is instantiated for every compact simple type, not only SU(2)/SU(3).
Checkable predicate: `WeylDimData` + `AxisFactorBound` (+ the
`ZtEtaModel` equalities) realized for the classical families
A_n/B_n/C_n/D_n at general rank and the five exceptionals — either by
rank-general lemmas (preferred; `WeylDimGeneral.lean` and
`RankCollapse.lean` are the seeds, and `rank_collapse` is already
validated across all 19 types) or by per-type instantiation — such
that `su3_uniform_witness`-style witnesses exist for a representative
of every type, and the general-rank statement is a theorem where the
Weyl data permits.

**Deliverables.**
- Lean: the per-family/rank-general data modules; witnesses; audit
  entries.
- `computations/` sweep extending the U.4 `Σ η(G) ≤ Σ η(su2)`
  corroboration across the realized types.
- A note on any type where the axis-factor bound needs a genuinely
  different argument (expected candidates: G₂/F₄ short-root
  normalizations — document the Killing-form convention per Rule-5
  precedent from Milestone 1.1).

**Dependencies.** 11.0. Independent track; good parallel work while
11.7/11.8 mature.

**Open questions.** Whether to state the final theorem over an
abstract `RepData`-with-verified-axioms class (cleanest) or an
explicit 19-case enumeration (most checkable); the audit script should
accept either.

**Composition update (2026-07-03).** The GPT review adds the missing
second half of this obligation: beyond *realizing* the per-group data,
Clay-readiness requires showing the `RepData`/`SimpleGroup`
abstraction is **equivalent to actual compact simple gauge groups**,
not merely parameterized by admissible data — i.e. a
classification-facing layer (compact simple types ⇒ verified `RepData`
instance, with the Casimir floor, heat-kernel tail, and Peter–Weyl
data as theorems per type). Add that faithfulness theorem to this
milestone's definition of done, so `mass_gap_simple_group` quantifies
over the groups themselves and not over an interface that might admit
non-group inhabitants.

---

### Milestone 11.13 — `ClayTargetPinned`: the surrogate-proof top-level target

**Status.** DONE (2026-07-03, statement-layer) — `lean/YMGap/Rubric/ClayTargetPinned.lean`: `ClayTargetPinned μ_inf` pins every clause to ONE shared physical stack (OSAxiomBundle + OSReconstruction + GNS over the SAME μ_∞), + `toClayTarget` coarsening; deliberately UNINHABITED (guard-protected), axiom-clean. Honest hardening: `GNSDataOfBundle` needs a `WilsonGNSData` param.

**Goal.** A new headline target structure that **cannot be inhabited
by surrogate, model, or existential data**, because every field is
pinned to the same physical construction: one `G`-indexed bundle
carrying the lattice approximation tower, the finite-volume measures,
THE continuum measure, THE gauge-invariant local observable algebra
(with Wilson-loop and curvature-polynomial field systems), THE OS data
and reconstruction, and THE Hamiltonian — with nontriviality,
local-field correspondence (11.17), asymptotic-freedom short-distance
behavior, axioms-at-least-OS/Wightman, and the mass gap all stated
**about those same objects**. The mass-gap clause returns its `Δ` as
`Σ` data with a `CReal.IsPositive` witness (Rule 2/8.3 corrections to
the review's `∃`-sketch). Checkable predicate: the module elaborates;
`ClayTargetPinned` is deliberately uninhabited; the OLD `ClayTarget`
is re-derived as a **proved coarsening** of the pinned target (a
`toClayTarget` projection in the `toFrontierC` supersession pattern),
recorded as the compatibility wrapper rather than the headline.

**Route notes.** Most referenced component types do not exist yet —
this is a *statement-layer* milestone (Rule 5: formalize the
statement; leave witnesses to their owning milestones). Reuse existing
carriers wherever they are already content-bearing (`OSAxiomBundle`,
`ContinuumMeasure`, `OSReconstruction`, `GNSComplete`); introduce new
interface types only where the pinning demands identity of objects
that today live in separate structures. The pinning is what makes
Rule 9(1) *mechanical*: a surrogate witness for one clause fails to
typecheck against the shared parameters instead of needing a human to
notice.

**Deliverables.**
- `lean/YMGap/Rubric/ClayTargetPinned.lean`: the structure, the
  `toClayTarget` coarsening, PROVED/OPEN docstring sections, axiom
  gates.
- Rubric relabeling pass: every clause currently green via a surrogate
  (the survival-product uniform-coupling floor is the known case) is
  labeled `MET-surrogate` with a pointer to the pinned clause that
  supersedes it.
- `FRONTIER` list update (12.2) adding `ClayTargetPinned`.

**Dependencies.** 11.0 (the MET-surrogate inventory). Schedule with
11.14 — they are the two architecture PRs.

**Open questions.** Whether `allCompactSimple : ∀ G, PhysicalYMData G`
should be a `Π`-field of one structure or a per-`G` family with a
separate universal statement — pick whichever lets 11.12's
faithfulness theorem plug in without re-plumbing.

---

### Milestone 11.14 — `FrontierDAG`: unify the enumerations, prove the bridges

**Status.** DONE (2026-07-03, items 1+2) — item 1: `Rubric/FrontierDAG.lean` (11-atom uninhabited DAG + `toSubWallA` + guard retarget). item 2: `Rubric/FrontierDAGBridges.lean` — all 4 suspected cross-list identifications ADJUDICATED: (i) Minlos≡Minlos PROVED equivalence (rfl, node merge); (ii) bulkCtrl↔hlocalize DOCUMENTED REFUTATION (per-mode vs per-scale arity mismatch; real link = `hbridge_of_hlocalize`); (iii) `qFloor_of_openTrueMargin` PROVED (FrontierDAG.trueMargin → `QFloor`); (iv) `finiteSMargin_of_crossRatio` PROVED CONVERSE (forward `CoreBBridge` stays open). Item 3 (anti-proliferation) DONE: `scripts/frontier_dag_check.py` + `make frontier-dag-check` (9 enumerations, 0 unbridged; `--self-test` 9/9) — a NEW frontier enumeration must carry a proved bridge to `FrontierDAG`.

**Goal.** ONE canonical audit surface for the open problem, replacing
the current situation of two overlapping enumerations plus scattered
ledger residuals. Checkable predicates, in increasing strength:
1. `lean/YMGap/Rubric/FrontierDAG.lean` exists: a single deliberately
   uninhabited structure whose fields are exactly the canonical open
   atoms — initially: the fusion local-CLT/`bulkCtrl` node, the
   Sub-wall A geometry nodes ((T′)-residue, (D1), pentagon; (D2) per
   its 11.1 status), `hbridge`-residue, the true physical margin, the
   physical Wilson bridge, the bounded Hamiltonian, the
   tightness/Minlos node, physical O(4) restoration, the
   all-compact-simple faithfulness node, the finite-s saddle margin,
   and the local-fields/OPE node (11.17) — each field typed by the
   EXISTING repo type it stands for (never a new abstraction when a
   named one exists).
2. **Bridge theorems** (the genuinely new content this composition
   elicited): proved mappings between the enumerations — e.g.
   `FrontierDAG → Tier0Scorecard`-inputs and
   `FrontierDAG → ReconstructionOpenFrontier`-inputs coarsenings in
   the `toFrontierC` pattern; and, for each *suspected* cross-list
   identification (Minlos ≡ Minlos; `bulkCtrl` ↔ `hlocalize`;
   `OpenTrueMargin` ↔ `UniformSpacingFloor` via 11.15), either a
   proved equivalence/implication or a documented refutation. Either
   outcome is knowledge: dedup collapses the frontier count;
   refutation exposes that the measure/RG and operator/OS sides need
   genuinely different inputs.
3. **Anti-proliferation regime active** (Rule 9 update): from this
   milestone on, a new frontier enumeration may only enter the tree
   together with a proved coarsening/refinement bridge to
   `FrontierDAG`; contributions close atoms by *deleting or weakening
   a DAG field via proof*, never by adding parallel scorecards.

**Deliverables.** The module; the bridge theorems; `docs/frontier-status.md`
regenerated to walk the DAG as its master list; the 12.2 guard
retargeted at the DAG.

**Dependencies.** 11.0 (the cross-list identification inventory);
11.13 (the DAG's target-side consumer). Bridge item for
`OpenTrueMargin` depends on 11.15.

**Open questions.** Granularity — whether DAG nodes are the coarse
tokens or the finest current residues (recommend: finest current
residue, with the coarse tokens derived, matching how
`Tier0Scorecard` refined `Tier0FrontierC`); whether edges
(dependencies between atoms) should be encoded as types or left to
the generated doc (start with the doc).

---

### Milestone 11.15 — `TrueMarginRecursionPhysical` and the target-adequacy lemma

**Status.** DONE (2026-07-03, statement+adequacy) — `Continuum/TrueMarginRecursionPhysical.lean`: the pinned additive-erosion recursion + `uniformSpacingFloor_of_trueMarginPhysical` (ADEQUACY GATE ANSWERED: the true physical margin SUPPLIES the shared `UniformSpacingFloor` floor). Axiom-clean. Residual (11.8-class): the `.step` inhabitant (ε_k erosion producer + anchor-dominates-budget); strictly sharper than the multiplicative-only `TrueMarginRecursion`.

**Goal.** The uniform-in-coupling clause on the Clay-facing path is
the **true dimensionless physical margin**, and the relationship
between the two existing candidates is settled by proof. Two parts:
1. **State the pinned recursion.** Building on the existing
   `UniformCouplingFromAF.TrueMarginRecursion` token: a structure over
   the physical transfer tower carrying `margin k = massLat k /
   spacing k` (definitional field), per-step control
   `margin (k+1) ≥ (1 − δ_k)·margin k − ε_k` with the defect
   schedules as data, a summability **modulus** for `Σ(δ_k + ε_k)`
   (data, not a bare `Summable` — Rule 8.3), and the positive-limit
   conclusion as `Σ' Δ, CReal.IsPositive Δ × EventuallyLowerBound`.
2. **The adequacy lemma (the gate for 11.8).** Prove
   `TrueMarginRecursionPhysical → UniformSpacingFloor` (the physical
   margin supplies the shared scalar floor all three routes consume)
   — in which case 11.8's target stands and the pinned recursion
   becomes its front door — OR establish that `UniformSpacingFloor`
   admits inhabitants the physical margin does not license (a
   surrogate-weakness witness), in which case the scorecard clause and
   11.8's predicate are retargeted at the pinned recursion and the
   floor is relabeled `MET-surrogate`-track.

**Deliverables.** The Lean structure + adequacy lemma (or refutation
record); replacement of the survival-product clause on the Clay-facing
path (the surrogate is retained, relabeled, as non-headline); scorecard
and DAG updates.

**Dependencies.** 11.0; feeds 11.8 (gate) and 11.14 (bridge node).
The analytic *discharge* of the recursion is 11.8-class research —
out of scope here; this milestone is statement + adequacy.

**Open questions.** The right constructive rendering of
`spacing → 0` (a modulus-carrying null sequence) and of
`EventuallyLowerBound` (reuse `CReal.leEv`); whether `δ_k` should be
identified with the graded bond-moving defect `≤ (1−w_k)²` from the
δ-loop chain (likely — record the identification in the DAG).

---

### Milestone 11.16 — The physical Wilson / Peter–Weyl bridge

**Status.** DONE (2026-07-03, single-bond + reduction) — `Continuum/PhysicalWilsonBridge.lean`: `physicalWilsonPeterWeyl` CLOSES the single bond (physical `cinner` = char-diagonal) modulo the sole primitive `AngleCosineIntegral` (∫cos kθ = πδ); the K-fold product assembly (`cprod_physPairing_diag/offdiag`) is proved; arbitrary-x `CharacterDiagResolution` REDUCED to (A) `PhysicalCharacterCoordinateMap` + (B) `HeatKernelReferenceWeight`. FINDING: the EQUALITY form is structurally UNSATISFIABLE (rational `E_Λ` vs irrational `reflWeight=e^{−tC₂}`) → DOMINATION is the right bridge.

**Goal.** Retire `OpenPhysicalWilsonBridge`: prove the Peter–Weyl /
Schur diagonalization **inside the actual physical inner product** —
link variables in `G^{E(Λ)}`, gauge action at vertices, the
invariant subalgebra, Haar integration, the Wilson plaquette weight —
rather than in the character-diagonal representation. The repo's own
honesty notes identify this as the standing `Q'`/CReal representation
boundary: the char-diagonal instance is discharged
(`WilsonSchurIdentities.wilsonSchurFormGap`), but the interacting
finite-volume moment functional is not that instance; and the OS2
closure's docstring concedes the diagonalized-basis *representation*
is the citable analytic input. This milestone converts that citation
into a theorem.

**Checkable predicate.** A theorem (shape:
`physicalWilsonPeterWeylDiagonalization`) establishing that the
reflection/spectral forms computed in the physical finite-volume inner
product (`cinner` over the `FiniteVolume.ReferenceWeight`
construction) coincide with (or are dominated by, where equality is
the wrong statement) the character-diagonal forms already proved —
discharging `WilsonSpectralBridge.CharacterDiagResolution` — so every
spectral-gap statement imports the physical bridge rather than the
surrogate.

**Route notes.** Ingredients exist: double-Haar Schur orthogonality is
finite representation theory (per-irrep exact `Q'` where matrix
coefficients are rational-representable; `CReal` where not);
`E2ProductFunctional`/`HaarClassIntegral` carry the product-Haar
functional; the cross-plane tensor factorization is already the
per-bond reduction pattern. The honest hard part is the interacting
weight insertion (the Boltzmann factor between characters) — the
character-expansion of the weight is the same machinery as the KP
activity bounds; start at one bond, one plaquette weight, then the
product assembly.

**Deliverables.** `lean/YMGap/Continuum/PhysicalWilsonBridge.lean`;
the retargeting of OS2/gap consumers; DAG/scorecard updates;
`notes/physical-wilson-bridge.md` recording exactly which prior
results were char-diagonal-conditional and are now unconditional.

**Dependencies.** 11.0. Independent of Sub-wall A; strengthens the
foundations under 11.5/11.6/11.11.

**Open questions.** Whether equality or two-sided domination is the
right bridge statement for the interacting functional (domination
suffices for every current gap consumer — prefer it if equality
forces irrational normalizations into `Q'` positions).

---

### Milestone 11.17 — The Clay local-field layer: curvature polynomials, stress tensor, OPE, short-distance AF

**Status.** DONE (2026-07-03, statement-layer) — `Continuum/LocalCurvatureFields.lean` (one module; concrete curvature-word polynomial grammar + stress-tensor/OPE-with-remainder-modulus/AF-short-distance interfaces, all faithful/non-vacuous/uninhabited): `content_discharges` — the uninhabited `LocalOperatorContent` bundle discharges BOTH bare `FourDExistence` carriers `GaugeGeneratedContent ∧ UVAsymptoticFreedomContent` via `gaugeGenerated_of_localCurvatureFields`/`uvAF_of_afShortDistance`.

**Goal.** The archive's Clay coverage gap — identified by the external
review and genuinely absent from both the repo and the earlier plan —
is closed at the *statement* layer: the Jaffe–Witten requirement is
not only measure + gap, but local quantum field operators
corresponding to gauge-invariant polynomials in the curvature and its
covariant derivatives, with short-distance behavior matching
asymptotic freedom / perturbative renormalization, including
stress-tensor and OPE expectations. Today the repo carries this as two
bare `Prop` fields (`gauge_content`, `uv_asymptotic_freedom` in
`FourDExistence`). Checkable predicate: content-bearing interface
structures — a curvature-polynomial–to–local-operator correspondence
(with gauge/Euclidean covariance and locality fields), an OPE-control
structure (coefficients, prescribed AF singularity bounds, explicit
remainder modulus as data), a stress-tensor slot, and a
short-distance-AF structure — wired into `ClayTargetPinned` so the
pinned target **cannot be inhabited without them**, replacing the two
bare `Prop`s.

**Route notes.** Statement-layer only (Rule 5): no analytic discharge
is scoped here, and the structures must be faithful and non-vacuous
(Rule 9(1)) — the OPE remainder is a modulus, the singularity bounds
name exponents, the correspondence quantifies over a concrete
polynomial grammar (a finite inductive type of invariant
curvature/covariant-derivative words), never `Prop := True`. Where the
lattice already has proxies (Wilson loops ≈ curvature holonomy;
`AFRateCalibration` ≈ the running-coupling data), record the intended
identification in docstrings so the eventual discharge has its
landing sites.

**Deliverables.**
`lean/YMGap/Continuum/LocalCurvatureFields.lean`,
`.../StressTensor.lean`, `.../OPE.lean`,
`.../AsymptoticFreedomShortDistance.lean`; the `FourDExistence` /
`ClayTargetPinned` rewiring; a `formal/` note mapping each structure
to the corresponding sentence of the official problem statement (this
becomes part of 12.1's faithfulness section).

**Dependencies.** 11.13 (the consumer). Independent of everything
else; good parallel statement-layer work.

**Open questions.** The right constructive home for "perturbative
renormalization agreement" (an asymptotic-expansion-with-modulus
statement vs. a bounds-only rendering — scope in the formal note
before committing the Lean type); whether the stress tensor deserves
its own correspondence instance or is one entry of the polynomial
grammar (start as one entry).

---

## Phase 12: Clay compliance, publication, and repository hygiene

### Milestone 12.1 — The frontier-reduction paper

**Goal.** A submission-ready manuscript: *"A machine-checked
constructive reduction of the Yang–Mills mass gap: fixed-spacing
closure and an eight-atom continuum frontier."* Contents: the
fixed-spacing constructive results (the `ClayFixedSpacingMet` line,
with the transcription argument for why the constructive predicates
faithfully render the rubric clauses — this faithfulness argument is
the paper's most attackable surface and must be a section, not a
footnote); the uniform-group reduction; the Tier-0 enumeration theorem
(`toFrontierC`, the routes-convergence theorem); and the honest status
map from `docs/frontier-status.md`. Extends the Phase 5.1 draft.

**Why now, not after closure.** It is independently publishable; it
starts the community-scrutiny clock the Clay rules require
(publication in a qualifying refereed outlet + waiting period +
general acceptance); and it recruits exactly the reviewers —
constructive-QFT (Bałaban-school) and Lean/Mathlib — who can attack
Phase 11's research core.

**Deliverables.** `formal/frontier-reduction-paper/` building to PDF;
an artifact-evaluation appendix (pinned toolchain `v4.29.1`,
zero-dependency `lake build`, audit reproduction instructions); arXiv
preprint; venue shortlist memo (candidates: a mathematical-physics
journal for the mathematics + an ITP/CPP-track companion for the
mechanization — decide in the memo, not here).

**Dependencies.** 11.0 (the status doc is a paper section). Benefits
from, but must not wait for, 11.1–11.6.

**Open questions.** One paper or two (math + mechanization); whether
to include the hierarchical-floor result if 11.8 lands in time.

---

### Milestone 12.2 — CI frontier guard

**Status.** DONE (2026-07-03) — realized as `lean/YMGapGuard.lean`, a Lean-reflection guard (a separate lib root run every `lake build`, fail-on-error CI step + `make lean-frontier-guard`). Fails the build if `Tier0Scorecard`/`UniformSpacingFloor`/`ClayTarget` acquires an UNCONDITIONAL inhabitant; conditional reductions pass; independent of `AXIOM_AUDIT.md`. `frontierTypeNames` is the extensible declared list; `frontierAllowlist` is the human-reviewed two-key hatch. Verified both directions (fire-tested on a real inhabitant). Variant note: implemented in Lean rather than as `scripts/frontier_guard.py`; the DAG-retarget (12.2 composition) lands with 11.14.

**Goal.** It is mechanically impossible for the repository to
*silently* claim more than it has proved. Checkable predicate: CI
fails if any declared frontier bundle (`Tier0Scorecard`,
`ClayScorecard.ClayTarget`, `UniformSpacingFloor`,
`SpectralMarginInput`, `SixJPentagon`, `ContinuumYMExistence`, plus a
declared-in-one-place extensible list) acquires an inhabitant whose
axiom set is not `∅`/`[propext]`/`[propext, Quot.sound]`, or whose
proof term elaborates through `sorryAx` — while a *legitimate*
inhabitant (axiom-clean, sorry-free) fails CI only until a human flips
the atom's status in the frontier list (a deliberate two-key
ceremony: closing a Clay atom must be an explicit act, mirroring
Rule 6's sign-off requirement).

**Deliverables.** `scripts/frontier_guard.py` (extends
`lean_axiom_audit.py`); the declared frontier list as data
(`lean/FRONTIER.md` or a `.toml`); CI wiring; documentation in
`lean/AGENTS.md` (done as part of this phase's doc refresh).

**Dependencies.** 11.0 (shares the bundle-walking machinery).

**Open questions.** Whether the guard should also protect against
*vacuous weakening* of a frontier type (e.g. a refactor that changes a
field to something trivially inhabitable) — a type-hash of the
frontier structures in the baseline is the cheap version; include if
low-cost.

**Composition update (2026-07-03).** Two refinements from the
composed reviews: (a) the guard's declared frontier list IS the
`FrontierDAG` (11.14) — one source of truth, walked by both the
status generator and the guard; (b) the type-hash protection is
promoted from optional to required for `ClayTargetPinned` and the DAG
itself, since the pinning (11.13) is load-bearing: silently loosening
a shared parameter is exactly the vacuous-weakening attack the pinned
target exists to prevent.

---

### Milestone 12.3 — `Continuum/` consolidation

**Status.** DONE (2026-07-03) — `docs/continuum-map.md` (the curated import spine: capstones, the four live chains, frontier leaves, guarded types, archive) + `docs/INDEX.md` pointer; `Tier0ReductionCapstone` archived to `lean/archive/` (superseded r2) + import removed; `AXIOM_AUDIT.md` regenerated (was stale: 2252 loop-era theorems untracked; now 6010 tracked, `make lean-audit-strict` PASS). KEY FINDING: the round/`*Close`/`*Progress` families are LIVE cumulative dependency chains, NOT superseded — mass-`Attic/` archival is not available without breaking the build; the map is the drift-reduction tool. `FusionCoreStepRound[A–J]`→1-file merge documented as a risk-flagged follow-up.

**Goal.** The ~470-file `Continuum/` directory is navigable by a fresh
reviewer: superseded iteration files (e.g.
`FusionCoreStepRound[A–J]`, retired `*Progress`/`*Close` drafts whose
content has been absorbed) are moved to `Continuum/Attic/` (still
building, still on disk, excluded from the default aggregator exactly
as `PolyAtlas`/`ModuliAlgebra` already are), and a generated import-
graph document maps the load-bearing spine from `Constructive/` to the
scorecards.

**Constraint.** Zero semantic changes: `lake build` output, the audit
baseline, and every theorem statement are unchanged up to module
paths; the axiom-audit script's tracked names are updated in the same
commit; the move list is reviewed against `YMGap.lean`'s existing
load-bearing/excluded annotation before anything moves.

**Deliverables.** The `Attic/` move (mechanical, scripted, reviewed);
`docs/lean-import-spine.md` (generated); updated `lean/README.md`
folder map (done in this phase's doc refresh).

**Dependencies.** 11.0 (its status table identifies what is
superseded). Do **not** interleave with active Phase-11 Lean work on
the same files — schedule as a quiet-window batch.

**Open questions.** Whether git history preservation across moves
matters for the paper's artifact evaluation (use `git mv`; note it in
the artifact appendix).

---

### Milestone 12.4 — External review campaign

**Goal.** At least two external experts — one constructive/rigorous
QFT (Bałaban-school lineage), one Lean/ITP — have produced written
feedback on (a) the faithfulness of the rubric transcription and (b)
the axiom-gate methodology, and the feedback is triaged into issues.

**Deliverables.** A reviewer dossier (the 12.1 preprint + a 10-page
reading guide: "what to check and how to check it," including the
one-command audit reproduction); an outreach shortlist; triaged
feedback log in `notes/external-review-log.md`; any resulting
statement-level fixes filed as Phase-11 amendments.

**Dependencies.** 12.1 preprint.

**Open questions.** Timing of Clay Institute contact — convention is
that the community-acceptance process runs through publication, not
direct submission; the dossier should follow the published rules for
the Millennium Prizes (qualifying outlet, waiting period, general
acceptance) and say nothing that presumes closure.

---

### Suggested near-term sequencing (composed queue, 2026-07-03)

Merging this plan's ordering with the external review's PR queue; each
item is small enough to be one reviewable change:

1. **11.0** frontier re-audit + unimported-file audit + `noncomputable`
   ledger + MET-surrogate inventory (architecture; fast).
2. **11.13 + 11.14(1)** `ClayTargetPinned` + `FrontierDAG` statement
   modules, with the `toClayTarget` coarsening (architecture; fast).
3. **11.1** the (D2) sufficiency note / L∞ tightening decision.
4. **11.15** `TrueMarginRecursionPhysical` + the adequacy lemma —
   gates 11.8 before heavy spend.
5. **11.2(A)+(C)** `CubicEulerBound` and the Prüfer/Cayley count — note
   the (P) leg is under active reduction in `PenroseDomInduction.lean`
   (modified 2026-07-03); coordinate rather than duplicate.
6. **11.5** discharge `hadd`; then **11.6** `hbridge` inputs.
7. **11.16** physical Wilson bridge, single-bond first.
8. **11.11(a)** finite-volume bounded `H = −log T`.
9. **11.7 first tranche** fusion-CLT ladder items 1–2 + the
   hierarchical prose campaign; **11.9(i)** Minlos quarantine in
   parallel.
10. **11.17** local-field/OPE statement layer; **12.1** paper draft
    begins as soon as 11.0/11.13/11.14 land (they are its status and
    faithfulness sections).

---

## Phase 13: Wall-closure execution paths (2026-07-09 review)

Written after a full review of the last ~25 commits, the capstone
(`docs/CAPSTONE-2026-07-06.md`), the burn-down ledger
(`docs/PROGRESS-LEDGER.md`), the routes adjudication
(`docs/alternative-routes-to-singlestep.md`), and the D1 audit chain
(`Ursell4DBridgePin` → `MayerUrsellZ4Physical` → `MayerUrsellZ4PhysicalClose`).
State at review: F = 1 (`singleStep` atomic), D = 0, guard = 5, C = 18;
fixed-spacing gap unconditional at every coupling (Peter–Weyl resummation);
(T′) discharged; (D1) discharged-as-typed but under-constrained (single-line
model); item 12 gated on finite-scale certification; `hlocalize` parked
pending a constructive-integral layer; A2 gated on the refuted-in-substrate
multivariate telescoping.

Ordering rationale: 13.1 and 13.2 convert open walls into theorems with
machinery already in-tree (highest discharge probability per unit work);
13.3 is the only known candidate for a LEGAL strictly-weaker decomposition
of the atomic core (ledger rule (b)); 13.4 hardens the primary bet (item
12) and kills its two known soundness gaps; 13.5–13.6 are the remaining
satellite atoms. Every item obeys the anti-loop rule: predicted outcomes
are stated, and any attack whose honest prediction becomes "another
`:= SingleStepDefectBound` alias" is aborted, recorded, not spawned again.

### Milestone 13.1 — (D1-loopy) the pinned multi-plaquette Penrose–Ursell domination

**Update (2026-07-09, session 5 — step 7, THE SIGN LAYER CLOSED AS
IDENTITIES).** `Continuum/XiAvoidanceCorrelation.lean`: the avoidance-
correlation inequality PROVED — `A₁₂·Ξ ≤ Av(b₁)·Av(b₂) + A₁₂·XiB2`
(`avoidance_correlation`, from the exact normaliser identity
`avoidance_mayer`: `A₁₂·Ξ + E·D ≃ Av₁·Av₂ + A₁₂·B`). BONUS: the truncated
two-point numerator pinned to its EXACT four-cell normal form
`T·Ξ² = A·B − E·D` (`truncated_numerator_mayer`) and the grand corollary
`truncated_numerator_le_chain`: `XiB2·Ξ ≤ XiB₁·XiB₂ + Ξ·(two-marker chain
majorant)` — the first PROVED upper bound on the truncated two-point
numerator, its diagonal exactly the (D2)-floored bridging sum. The residual
is now a SHARPNESS question (the connectedness cancellation `A·B` vs `E·D`
— extracting the separation-DECAYING envelope for the difference), not a
sign question. First-try green, axiom-clean.

**Update (2026-07-09, session 4 — step 6, THE SIGN LAYER OPENED).**
`Continuum/XiSignLayer.lean`: the truncated two-point correlator's Ursell-sign
content is now an EXACT SUBTRACTION-FREE IDENTITY — `two_point_mayer`:
`XiB2·Ξ + Av(b₁)·Av(b₂) ≃ XiB(b₁)·XiB(b₂) + A₁₂·Ξ` (four-cell avoidance
partition of the compatible families + the 4-variable degree-2 polynomial core
`cell_expand`, PROVED BY THE REFLECTIVE RING NORMALISER — its first live
payload on the (D1) chain). Corollary `XiB2_mul_le`: the truncated numerator
is dominated by the product term + the double-avoidance term. The whole
remaining sign content is thereby ISOLATED in ONE inequality: the
avoidance-correlation bound (`A₁₂·Ξ` vs `Av(b₁)·Av(b₂)` + chains) — the
genuine connected-chain content, named in the module docstring. Axiom-clean.

**Update (2026-07-09, session 3).** Steps 4–5 landed: `XiPinnedBridge` (`8278654`) — the ONE-POLYMER-BRIDGE Mayer bound `XiB ≤ actSum(bridges)·XiR` PROVED (axioms `[propext]` only); `XiChainBound` — the TWO-MARKER raw-pair domination `XiB2 ≤ actSum(br₁∧br₂)·XiR + actSum(br₁)·XiB(br₂) + actSum(br₂)·XiB(br₁)` PROVED (`XiB2_le_chain`/`XiB2_le_product`/`XiPair_le`, `[propext]` only) — the upper envelope of `⟨1_p1_q⟩·Ξ` by diagonal + cross products. Remaining on this front: the TRUNCATED-correlator subtraction (the genuine Ursell-SIGN layer — verified along the way that hard-core gases are NOT negatively correlated, so the chain term is real physics, not bookkeeping) + the shared R1 identity.

**Status.** CURRENTLY IN PROGRESS (2026-07-09, A1-side DISCHARGED at the pinned loopy instance) — branch `d1-loopy-penrose-ursell`, commits `1971221` + `6e50823`: `DecoderReachFloor` (the DFS-decoder distance invariant — (D2) `z4dist` LOAD-BEARING on the (D1) chain for the first time; `enum_reach_floor`: reach ≥ d ⟹ size ≥ d+1 for the REAL decoded enumeration) + `LoopyPinnedPenroseUrsell` (`loopyOffCorr` COMPUTED from the decoded animal enumeration, `loopy_penrose_ursell` PROVED via prefix-vanish + termwise KP domination; inhabits `PenroseUrsellDatumG` and `BridgeDecomposition`, decays at `ρ4 ≃ 15/32`, non-vacuous by an explicit decoded bridging animal; `stage1Loopy_pinned`: the A-side capstone now reduces to A2 ALONE). Residual sharply named (see `notes/d1-loopy-closure.md`): the Ursell-sign layer for the two-point `Xi`-ratio (finite-volume polynomial identity, ring-normaliser territory — next attack) + the shared R1 `AbstractRealPartitionIdentity`. Build 789 green, guard 5, statement guard no-drift, audit-strict PASS, axiom-clean.

**Goal.** Inhabit `Stage1LoopyReduction.PenroseUrsellDatumG
(z4ClusterCountBound p) w4 gr` with `offCorr` PINNED to a genuine
finite-volume MULTI-PLAQUETTE (loopy) correlator — closing the
under-constraint caveat of `4c7c114` (whose inhabitant is the single-line
`reconTransfer`). Checkable predicate: an inhabitant whose `offCorr` is
computed from a finite polymer partition function (the `Xi`/`Zreal` layer,
or a finite-volume two-point ratio built from `enumPolys`), with a proved
non-vacuity certificate (`offCorr` not identically zero off-diagonal, and
provably ≠ any single-mode `reconTransfer` correlator), and
`penrose_ursell` PROVED, not carried.

**Current best route (finite-volume-first).** At finite volume every
object is a FINITE `Q'` sum over `enumPolys`, so the Mayer–Ursell
expansion is a polynomial identity — exactly the ring normaliser's
payload (`13dcf3e`). Three proved ingredients compose: (i) the algebraic
connecting-cluster expansion identity at finite volume (the genuinely new
Lean content; prove for cluster size ≤ small `n` by `decide`/normaliser
first, then the general induction); (ii) the per-cluster tree-graph
majorant — (T′), DISCHARGED (`a56ae2f`); (iii) the size floor
`connected_spanning_size_ge` — (D2), CLOSED. Note the previous inhabitant
BYPASSED (D2) via the head-term route; the loopy statement is precisely
where (D2) becomes load-bearing — stop bypassing it. Volume-uniformity is
free: `connTailPartialG_decay` is uniform in the truncation length `N`,
so the datum's `tailLen` absorbs the finite volume.

**Deliverables.** `Continuum/LoopyCorrelatorPinned.lean` (the pinned
finite-volume correlator + non-vacuity), the expansion-identity module,
the inhabitant wired through `Stage1Loopy.decay`;
`notes/d1-loopy-closure.md` recording where the Lean deviates from
Friedli–Velenik Ch. 5 / Ueltschi 2004.

**Dependencies.** (T′) done, (D2) done, ring normaliser done, 11.3
statement work done.

**Open questions.** Whether `offCorr` should be the `Xi`-ratio (needs a
positive-denominator certificate at `w4`, available from `kpRatio =
15/32 < 1`) or the subtracted two-point finite sum (no division; likely
the constructive-friendly choice).

### Milestone 13.2 — `hlocalize` discretized: fusion local-CLT via reflected lattice paths **[research]**

**Update (2026-07-09, session 5 — step 5, general-`N` tail + a pointer
correction).** `Continuum/BoxSumTailGeneral.lean`: the general-`N` mode tail
`2N < s → boxSum w N s ≃ 0` (`boxSum_tail`) + `boxSum_cross_tail_le`
(the Cauchy–Binet cross product is trivial for `2N ≤ s`), replacing the
per-`N` tail lemmas — every future pointwise push of the box core owes only
the FINITE window `s < 2N`. POINTER CORRECTION for this milestone's
"weighted `strongCoupling` interlacing" front: the in-repo state is further
along than this file's earlier notes implied — `CoreStep` is already
machine-REFUTED for `N ≥ 2` (`FusionCoreStep`, round A), the box core is
inhabited pointwise at `N ≤ 4` (`w = 1/2`), and the honest uniform residual
is `UniformBoxLogConcave w` (the all-`N` direct box Cauchy–Binet = the
heat-kernel local-CLT content). The 13.2 discrete layer (ladder, parity-TP₂,
CB₂, `kpow_TP2_j1`) plus the ballot-formula/LGV row wall are the routes INTO
that residual; do NOT re-attack `CoreStep`.

**Update (2026-07-09, session 5 — step 4, ALL-p PARITY-TP₂ + a route
adjudication).** `Continuum/KpowParityTP2.lean`: the p-step `j = 1` fusion
kernel is parity-TP₂ for EVERY `p` (`kpow_TP2_j1` — CB₂ iterated through
the kernel-generic `pair_exchange_row_j1`, with parity propagation
`kpow_parity`; odd intermediate shifts vanish by row parity). ADJUDICATION
BANKED: the "extract row log-concavity via kernel symmetry" hope is
CORRECTED — TP₂ of a kernel does NOT yield log-concavity of a single row
(a row is not a 2×2 minor; propagation needs higher-order TP or the
convolution/PF₂ setting). The honest routes to the all-`p` row statement
(`pathCount` log-concavity): (i) the explicit ballot-number formula layer,
or (ii) an LGV path-pair injection — both finite combinatorics, both open.
`kpow_TP2_j1` is the two-row comparison payload the weighted
`strongCoupling` interlacing consumes. First-try green, axiom-clean.

**Update (2026-07-09, session 5 — step 3, CB₂ LANDED).**
`Continuum/KernelCB2.lean`: the 2×2 Cauchy–Binet/Karlin composition brick
PROVED in subtraction-free exchange form over `Nat` — `comp_TP2` (pair the
double-sum terms `(m,n)/(n,m)`; scalar core `cross_mul_le`:
`y≤x → v≤u → xv+yu ≤ xu+yv`; square-border decomposition `nsum2_succ`;
pair-exchange `nsum2_exchange`; `nsum_mul_nsum`). Payoff: the TWO-STEP
`j = 1` fusion kernel is parity-TP₂ (`compStep_TP2_j1`) — the odd
intermediate shifts vanish by parity forcing (`stepN_parity`), so the
exchange hypothesis holds for ALL pairs. First-try green, axiom-clean.
NEXT: iterate to the p-step kernel (all-`p` parity-TP₂ by induction on
`comp`), extract row log-concavity via kernel symmetry
(`fusionOK a j s = fusionOK s j a`), then the weighted `strongCoupling`
cross-parity interlacing toward `cauchyBinet`.

**Update (2026-07-09, session 3 — step 2, the TP₂ route adjudicated).** `Continuum/FusionParityTP2.lean`: TWO machine refutations banked — the raw fusion kernel is NOT TP₂ (parity interlacing, axiom-FREE), and parity-consistent TP₂ ALSO fails for `j ≥ 2` (the REFLECTION CORNER `a+s ≥ j` is load-bearing; a false pen-and-paper lemma caught by the failing kernel check). The corrected brick PROVED: corner-aware parity-TP₂ (`fusionOK_TP2_step`/`stepN_TP2`), with the `j = 1` fundamental kernel unconditionally parity-TP₂ (`stepN_TP2_j1`). Consequence for the campaign: no unweighted TP₂/Karlin composition reaches `cauchyBinet`'s mixed-parity index — the cross-parity comparison must come from the `strongCoupling` weights (at `N = 1` the claim is exactly `c₁² ≤ 3c₀²`). Next: same-parity log-concavity via Karlin composition of the corner-aware brick (or LGV), then the weighted interlacing.

**Status.** CURRENTLY IN PROGRESS (2026-07-09, step 1 landed) — `Continuum/FusionBratteli.lean`: `fusionOK_iff_ladder` PROVED (the Clebsch–Gordan LADDER normal form of the in-repo fusion indicator — the exact interface both the TP₂ and LGV routes consume) + `pathCount j p s` (the p-fold reflected-walk count, the discrete carrier of the fusion multiplicity) + kernel-checked anchors: the `j = 1` return counts are the CATALAN numbers (1, 2, 5, axiom-FREE `decide`), and the `p = 4` endpoint profile `(2, 3, 1)` is already log-concave — the shape of the campaign claim. Next: the log-concavity of `pathCount` in the endpoint (TP₂/Karlin or LGV injection), then the weighted upgrade to `boxSum` and the discharge of `FusionConvLogConcaveCore.cauchyBinet`. Axiom-clean.

**Goal.** Discharge the `FusionConvLogConcaveCore` /
`CurvatureEnvelope` wall WITHOUT the constructive-integral layer (the
"largest single Lean lift" flagged in the 2026-07-05 plan, Track C).
Reformulation: p-fold SU(2) fusion multiplicities ARE reflected
ballot-path counts (the SU(2) Bratteli diagram is a walk on ℕ with a
wall at 0), so the p ≥ 2 local-CLT/log-concavity claims become FINITE
combinatorics in the spin endpoint — Lean-core-native.

**Current best route.** Two independent attacks, adjudicate then commit:
(i) TOTAL POSITIVITY — the one-step fusion kernel is TP₂;
TP₂ composes (Cauchy–Binet) and TP₂ convolution preserves
log-concavity (Karlin), so the p-fold kernel's log-concavity follows by
induction from the elementary Jacobi/JW factorization (this is where the
`a2_jwtower` scouting already points); TP₂ at each finite level is
decide-checkable. (ii) DIRECT INJECTION — Lindström–Gessel–Viennot-style
path-pair injection proving log-concavity of the reflected-walk counts
bijectively. `CurvatureEnvelope`'s second-difference lower bound then
becomes discrete convexity of these counts, with tails via the existing
ϑ₃ engine. Predicted outcome: a genuine discharge of `uniform_in_m`'s
open wall (a real partial result; per the adjudication it does NOT
shrink the atomic core — say so in the commit).

**Deliverables.** The path-count = fusion-multiplicity identity
(decide-checked at low spins, then proved); the TP₂ or LGV log-concavity
theorem; the wiring into `FusionConvLogConcaveCore`.

**Dependencies.** None open (JW tower scouting docs; ϑ₃ engine).

**Open questions.** Whether the reflection (wall at 0) breaks the plain
LGV involution and TP₂ is the safer primary; whether `CurvatureEnvelope`
needs strict log-concavity (path counts give non-strict at the boundary
— check the consumer's tolerance).

### Milestone 13.3 — ε-split adjudication: small-field/large-field decomposition of `singleStep` **[the one candidate legal F-split]**

**Status.** DONE (2026-07-09, session 6) — **ADJUDICATED: EQUI-INHABITS
(C++); the split is NOT a strictly-weaker independent decomposition.**
`Continuum/EpsSplitAdjudication.lean` (all axiom-clean): PRODUCER
`singleStepProp_of_split` ((i)∧(ii) → `SingleStepProp` at the coarse rate,
via the new `Q'` order-cancellation `le_add_cancel_right`); CONVERSE
`split_of_singleStepProp` (the core inhabits BOTH conjuncts at zero loss —
the pair equi-inhabits); VACUITY `pertStep_vacuous` (conjunct (i) alone is
satisfiable for every rate/margin by the loss that swallows the step — no
content); LOAD TRANSFER `absorb_forces_nonpos` (against the vacuous loss,
conjunct (ii) forces the coarse step nonpositive — refuted on every
positive-margin instance: the whole `singleStep` load lives in (ii)).
**The last named candidate F-split is dead; F = 1 (atomic `singleStep`) is
STRENGTHENED.** Surviving content is a CONSTRUCTION task, not a
decomposition: pin the loss to a constructed finite-volume large-field
functional (chessboard/RP) and prove `AbsorbProp` for it — front (a),
where item 12 / Milestone 13.4 continues. Do NOT re-attack this split.

**Goal.** Adjudicate the split `ε_k = ε_k^pert + ε_k^np` with two named
atoms: **`PerturbativeDefectOrder`** — the ≤ 2-loop part of the
block-spin defect is O(g⁴) with explicit constant (the physics content
of `EpsilonSummability`'s "ε_k quadratic ⟺ budget closes": one-loop
defects cancel, g_k⁴ ~ 1/k² summable) — a FINITE-dimensional certified
group-integral computation, exactly the Q'/normaliser substrate's
strength; and **`LargeFieldSuppression`** — the non-perturbative
remainder is ≤ C·e^{−c/g_k²} (super-summable), needing only CRUDE
stability bounds (chessboard/reflection-positivity estimates held
unconditionally in-tree + character positivity), NOT the sharp Balaban
chain — the numerical safety factor 45 is the slack that makes crude
constants admissible.

**Checkable predicate.** PROVE `(PerturbativeDefectOrder ∧
LargeFieldSuppression) → SingleStepDefectBound` AND certify at least one
conjunct strictly weaker (the `tm`-independence test used in
`ResummationAdjudication`/`SITE1PerMoveDefect`). If either direction
forces equi-inhabitation: record the C++ verdict, close the milestone as
REFUTED, do not campaign.

**Dependencies.** `EpsilonSummability`; the RP/chessboard modules; the
adjudication template.

**Open questions.** Where to draw the small/large-field threshold so the
two atoms stay independent (a `g_k`-dependent field cutoff is the
standard Balaban choice); whether `PerturbativeDefectOrder` should be
stated per-channel (composing with item 12's truncation) — prefer yes.

### Milestone 13.4 — Item-12 hardening: Taylor models in `u = 1−w` + derived channel coefficients

**Literature note (2026-07-09, user-supplied).** *"Spectral-Gap
Hypercontractivity Fails on S⁴"* (complementary note to Frank–Ivanisvili
2021): the critical log-Sobolev inequality fails on S⁴ (explicit zonal
Gegenbauer `C^{(3/2)}` test function, exact rational spectral ledger),
settling the case Frank–Ivanisvili left open (`n ≤ 3` sharp, high `n`
false). Relevance: (a) BANKED as further evidence for the item-15
adjudication (`docs/alternative-routes-to-singlestep.md`) — LSI/
hypercontractivity routes to `singleStep` are DIMENSION-FRAGILE at exactly
the borderline; SU(2) ≅ S³ sits on the sharp side (`n = 3`), so any future
LSI-flavored attempt must be S³-specific — treat critical-constant LSI
arguments near `n = 4` as presumptively dead. (b) METHOD reference for
13.2's weighted interlacing: exact zonal/ultraspherical computations
(rational `N_d` norms, generating-function coefficient extraction) are the
same exact-rational spectral-ledger style as the `coeffW`/ϑ₃ machinery;
SU(2) characters are the `C^{(1)}` (Chebyshev-U) column of the same
Gegenbauer family. Not load-bearing for 13.4.

**Status.** CURRENTLY IN PROGRESS (2026-07-09, session 6 — step 1 landed) —
`Continuum/TaylorModel.lean`: the Taylor-model layer over the certified `QI`
kernel, all `[propext]`-only. Horner `evalPoly` (no `pow`) with
`eqv`-sound coefficient add/scale; **THE UNIFORMIZATION MECHANISM PROVED**:
`evalPoly_le_of_coeffLeB` — one kernel-`decide`-checkable coefficientwise
certificate implies the pointwise polynomial inequality for EVERY `u ≥ 0` —
and `models_le_of_cert` — one coefficient `decide` + one remainder-endpoint
`decide` bound `f ≤ g` on the whole `[0, u₀]` (replacing per-scale interval
certification along the `w_k → 1` tail; `coeffLeB` restructured structural-
on-first so the kernel reduces it under `decide` — axiom-FREE demo
certificate checked). Step-2 target NAMED (`TMDefectCertificate`, deliberately
uninhabited) with its producer PROVED (`defect_le_sixUsq_of_cert`: a
certificate yields the uniform `defect(u) ≤ 6u²` on the whole domain, the
`singleStep`-shaped quadratic decay). NEXT (step 2): derive the pilot's TM
coefficients from the Peter–Weyl channel expansion at `w = 1 − u` (killing
the FREE-coefficient under-constraint), enclose the truncation tail into the
remainder via the ϑ₃ engine, and inhabit `TMDefectCertificate` on an
explicit `[0, u₀]`. Requires `tmMul` (nonneg-coefficient case suffices for
the heat-kernel expansion) — queued.

**Update (2026-07-09, session 7 — step 2 first half landed).**
`Continuum/TaylorModelStep2.lean` (all `[propext]`; certificate axiom-FREE):
`mulC`/`evalPoly_mulC` (Horner convolution product, `eqv`-sound);
`evalPoly_mono_u` + `rangeNonneg`/`contains_rangeNonneg` (nonneg-coefficient
range enclosure `[0, p(u₀)]`); **`tmMulN`/`models_mulN`** — sound
Taylor-model multiplication (`(P+r)(Q+r') = PQ + [P·r' + Q·r + r·r']`, cross
terms through the range intervals) — the arithmetic the derived channel
polynomials compose with. **`pilot_defect_uniform`** — the pilot
certification UNIFORMIZED: for any channel coefficient functions
nonnegative and under the pilot upper enclosures uniformly on `[0, u₀]`,
the truncated defect `(Σ c_j(u))·u² ≤ 6u²` at EVERY `u` at once, certificate
= ONE kernel `decide` (`pilot_hi_sum_cert`: `Σ hi_j = 39/10 ≤ 6`) — the
whole tail `w ∈ [1−u₀, 1]` replacing the single `w = 4/5` point. DESIGN
FINDING recorded: constant-enclosure channels lose `u²`-locality through
`tmMul` (all content lands in the remainder), so the pilot uniformization
uses the ONE-SIDED assembly; two-sided TMs are for the polynomial
Peter–Weyl channels. REMAINING (step 2 second half): derive the channel
polynomials `(1−u)^{C₄(r)}` (signed binomials — exact TMs with zero
remainder; the leading channel `heatKernelSep(1−u) = (1−u)³ ↦ [1,−3,3,−1]`
first), prove the uniform enclosures from them (discharging
`pilot_defect_uniform`'s hypothesis), ϑ₃ tail into the remainder, inhabit
`TMDefectCertificate`.

**Update (2026-07-09, session 8 — step 2 second half, part 1: the channel
enclosures DERIVED).** `Continuum/HeatKernelChannelTM.lean` (first-try
green, all `[propext]`): the uniform channel enclosures are now PROVED for
the exact Peter–Weyl channel form — `hk_channel_le`: `d·(1−u)^n ≤ d`
uniformly on `u ∈ [0,1]` (via `one_sub_nonneg`/`one_sub_le_one`, the
`le_add_cancel_right` window lemmas, and `qpow_le_one` on the shrunken
coupling); **`hk_defect_uniform`** — the PARAMETRIC certificate: any four
exact heat-kernel channels `d_j·(1−u)^{n_j}` with `Σd_j ≤ 6` (one kernel
`decide`) give the truncated defect `≤ 6u²` at EVERY `u ∈ [0,1]`;
`pilot_hk_defect_uniform` — the concrete instantiation at the pilot's
certified amplitudes (`Σ = 39/10`) and the GENUINE Casimir exponents
`C₄(j) = j(j+2)` — the channel `u`-dependence is now the real heat-kernel
decay, not a constant enclosure. REMAINING (named): the AMPLITUDE
IDENTIFICATION — that the true fused block-spin coefficients are dominated
by exact heat-kernel channels at these amplitudes (the item-9 fusion
normalization) — plus the ϑ₃ truncation tail into the remainder and the
`TMDefectCertificate` assembly.

**Goal.** Kill the two known soundness gaps of the primary bet
(`IntervalArithmetic.lean` / `TruncatedBlockSpinContraction.lean`):
(a) the pilot certifies ONE coupling (`w = 4/5`) but the obligation is
uniform along `w_k → 1`; (b) the truncated map's coefficients are
SUPPLIED, not derived (the FREE-coefficient instance of the `69f2e0f`
under-constraint finding).

**Current best route.** (a) Upgrade `QI` to TAYLOR MODELS in `u = 1−w`:
polynomial enclosure + interval remainder, all operations rational —
then the certification target becomes ONE decide-checked polynomial
inequality `defect(u) ≤ 6u²` valid on `(0, u₀]`, replacing per-scale
certification with a single certificate + the already-proved AF
summability (`invRunningCoupling_strictMono` ⟹ Σ(1−w_k)² < ∞). This is
the completed Koch–Wittwer proof shape (finite window + one
parameterized certificate). (b) Derive the channel coefficients from the
Peter–Weyl layer (`w^{C₄(r)}` + finite character-convolution rationals,
enclosures via the ϑ₃ engine that proved `TruncationTailBound`) and
re-type the truncated map so coefficients are THESE rationals — the
enclosure is then a theorem, not an input.

**Deliverables.** `Constructive/TaylorModel.lean` (sound ops +
composition, gated); the re-typed truncated map; the single
`defect(u) ≤ 6u²` certificate at the pilot truncation order.

**Dependencies.** `IntervalArithmetic.lean` (done), `TruncationTailBound`
(done), Peter–Weyl resummation modules (done).

**Open questions.** The remainder-form choice (Lagrange vs geometric
tail) for rational composability; `u₀` (take the certified
strong-coupling window's edge — the crossover window then needs finitely
many pointwise certificates, count them explicitly).

### Milestone 13.5 — (A2) the pentagon diagrammatically: Kauffman–Lins recoupling + certificate CHECKING

**Status.** NOT STARTED.

**Goal.** Prove the Biedenharn–Elliott content of
`SixJRecoupling.biedenharn_elliott` WITHOUT multivariate creative
telescoping (structurally refuted in-substrate, `bcacea2`: factorial-
degree Wegschaider certificates exceed decide capacity).

**Current best route.** (i) PRIMARY — the pentagon is a FINITE
Temperley–Lieb diagrammatic isotopy (Kauffman–Lins recoupling): prove it
by structural induction over Jones–Wenzl idempotents, i.e. finite linear
algebra over `Q'` at rational specializations — no hypergeometric
summation anywhere; this is the natural continuation of the
`a2-wenzl-tl`/`a2_jwtower` scouting. (ii) FALLBACK — certificate
CHECKING, not finding: generate the Wegschaider certificate OFFLINE
(HolonomicFunctions), import it as data, VERIFY with the ring normaliser
(verification is polynomial-identity checking — the refuted part was
in-substrate finding). Signs/irrationality handled as in the Tier-A
squared-Racah artifact: `6j²` ∈ `Q'` + a finite sign character.

**Deliverables.** The JW/TL pentagon module; or the certificate-import
format + verifier run; the wiring into `PartitionBeyondTree`.

**Dependencies.** Ring normaliser (done); JW tower docs.

**Open questions.** Which rational specialization of the TL parameter
the `Xi`/`Zreal` layer actually consumes (match it before proving);
whether the fallback certificate's size fits the normaliser's proved
capacity (measure on the smallest nontrivial pentagon first).

### Milestone 13.6 — Full `H₄` invariance + the phantom-parameter guard

**Status.** NOT STARTED.

**Goal.** (a) Extend `o4_restoration_H4` (`c6b82b4`, one axis
transposition) to the FULL hypercubic group (384 elements,
decide-friendly): invariance of the Schwinger functionals under the
generated group, and an explicit DAG note parking full O(4) restoration
BEHIND `singleStep` (the continuum upgrade needs only equicontinuity of
the convergence modulus over `H₄` orbits, which rides on the same
cluster-expansion smoothness — it must never be attacked as an
independent analytic wall). (b) MECHANIZE the `69f2e0f` under-constraint
finding: extend the statement guard to FLAG phantom-parameter frontier
structures — auto-attempt a `castBridge`-style transport for each
guarded structure's parameters; if one elaborates, the type is
under-constrained and the build fails (this is exactly the check that
would have caught both (D1) traps and the item-12 free-coefficient gap
mechanically).

**Deliverables.** The `H₄` group module + invariance theorem; the
phantom-parameter guard wired into CI next to the statement-hash guard
(`bb82e0a`).

**Dependencies.** (a) none; (b) the statement-guard machinery.

**Open questions.** Whether the transport auto-attempt is cheap enough
for every build (if not: run in the same CI tier as the dag-check).

### Suggested sequencing (2026-07-09)

13.1 (in progress, this session) → 13.2 (a real discharge available to
finite combinatorics) → 13.3 (one-session adjudication; the only
candidate legal F-split) → 13.4 (hardens the primary bet) → 13.5 → 13.6.
13.6(b) is small and can be interleaved anywhere.

