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

## Cross-cutting policies

### Constructive law

Every existence claim in code must return an explicit witness. No
function may return `True` or `1` as a "proof"; it must return the
witnessing object (the bound, the modulus, the KP pair). This is
enforced by the `validate()` methods on the dataclasses.

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

As of repository initialization: Phase 0 in progress. No milestones
closed.

To find the next task, locate the lowest-numbered milestone whose
dependencies are all closed and whose deliverables are not yet
complete.