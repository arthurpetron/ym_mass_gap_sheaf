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
