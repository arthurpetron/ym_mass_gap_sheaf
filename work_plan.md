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

As of 2026-05-24: Phases 0--2 are structurally closed, and Phase 3
is structurally complete through the SU(2) pilot validator. The
status is no longer "placeholder success"; the post-3.1 small-field
upgrade makes the default pilot fail outside the current weak-coupling
window.

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
3. **P3.4 $\eta$ coupling.** The relationship
   $\Delta_{\cap}\mapsto \eta$ is still the placeholder
   $\eta = 0.5\,\Delta_{\cap}$.
4. **P1.2/P1.3 heat-kernel normalization audit.** The current notes
   carry both inverse-coupling and diffusion-time language. Since a
   genuine heat kernel $K_t$ on a compact group concentrates at the
   identity as $t\downarrow 0$ and tends to Haar as $t\to\infty$, the
   use of `t = 2N/g^2` as heat-kernel time must be audited before
   character-expansion constants are treated as probability bounds.
   The buffer-shell note already exposes the related Haar-floor issue.
5. **Lean sorries.** `lean/SORRY_LEDGER.md` records the open
   `[P2.1]` and `[P2.3-{sf,lf,cap,sigma}]` obligations plus the
   assembled `step_obligation_witness`; all remain `sorryAx`-only.
6. **Continuum limit, OS reconstruction, and the mass-gap theorem.**
   These remain outside Phase 3 and are not implied by the pilot.

## Suggested next milestone

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
