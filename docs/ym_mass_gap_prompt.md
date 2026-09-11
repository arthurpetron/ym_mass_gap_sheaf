# PROMPT FOR "A CONSTRUCTIVE, MACHINE-CHECKED PROOF OF YANG–MILLS EXISTENCE AND MASS GAP"

*This document contains the full prompt for the agent campaign directed at a
complete, constructive, machine-checked resolution of the Clay Millennium
Problem "Yang–Mills Existence and Mass Gap" in the `ym_mass_gap_sheaf` Lean 4
development.*

---

## Current task statement

A **quantum field theory** here is a theory satisfying axiomatic properties at
least as strong as the Wightman axioms (Streater–Wightman) or, equivalently
via the Osterwalder–Schrader reconstruction, the Osterwalder–Schrader axioms
for Euclidean Green's functions. The Hilbert space **H** carries a positive-
energy representation of the Poincaré group with a vacuum vector Ω unique up
to phase, HΩ = 0. A theory has a **mass gap** Δ if the Hamiltonian H has no
spectrum in the interval (0, Δ) for some Δ > 0; the supremum of such Δ is the
mass m, and m < ∞ is required. **Non-trivial** means the theory has local
quantum field operators in correspondence with the gauge-invariant local
polynomials in the curvature F and its covariant derivatives (such as
Tr F_ij F_kl(x)), whose correlation functions agree at short distances with
the predictions of asymptotic freedom and perturbative renormalization theory,
including the existence of a stress tensor and an operator product expansion
with the prescribed local singularities.

Resolve the Yang–Mills Existence and Mass Gap problem completely, in the exact
form fixed by the Clay Mathematics Institute's official problem description
(Jaffe–Witten):

> **Yang–Mills Existence and Mass Gap.** Prove that for any compact simple
> gauge group G, a non-trivial quantum Yang–Mills theory exists on ℝ⁴ and has
> a mass gap Δ > 0. Existence includes establishing axiomatic properties at
> least as strong as those cited in Streater–Wightman [45] and
> Osterwalder–Schrader [35].

The official description specifically excludes weak-existence (compactness
arguments) as the solution to the existence part, unless other techniques
also establish the properties of the limit — the mass gap and the axioms.
The gap must be uniform in the volume: existence of a uniform gap for
finite-volume approximations followed by control of the infinite-volume
limit T⁴ → ℝ⁴, or an equivalent route, is part of the problem, not an
optional refinement.

Assume for purposes of this task that a complete affirmative proof exists.
The job is to construct it. A complete solution must prove exactly the
following, and it must be machine-checked:

**For every compact simple gauge group G, a non-trivial quantum Yang–Mills
theory exists on ℝ⁴ satisfying axioms at least as strong as
Wightman/Osterwalder–Schrader, and it has a mass gap Δ > 0 — formalized in
this Lean development, building green, with every theorem on the critical
path axiom-clean (`#print axioms` ⊆ {`propext`, `Quot.sound`}), both
statement guards passing, and the frontier types discharged (not weakened,
not renamed, not restated).**

Partial progress does not count unless it implies exactly the resolution
above. In particular, the following are insufficient:

- proofs for a truncated, lower-dimensional, abelian, Higgsed,
  supersymmetric, large-N, or otherwise severely simplified surrogate of
  four-dimensional pure Yang–Mills;
- construction of the theory on a compact space-time without the uniform gap
  and the infinite-volume limit;
- weak-existence/compactness constructions without control of the limit's
  properties (explicitly excluded by the official description);
- a gap for the lattice theory at fixed spacing, or at strong coupling only,
  without the continuum limit;
- reductions of the problem to another unproved statement, however sharp —
  a reduction converts the problem into a new open front and is the START of
  the next attack, never a deliverable;
- inhabitation of any frontier type by axioms, `sorry`, `native_decide`,
  classical choice, or vacuous instances;
- any bound, amplitude, or constant obtained from measurement or Monte-Carlo
  estimation rather than derived in-substrate (MCMC is scouting only; no
  measured number may enter any proof);
- computational verification of any finite family of cases;
- an essay on why the problem is hard.

## Standing structure of the campaign

The proof is to be produced **constructively/intuitionistically** in the
existing substrate: exact rationals (`Q'`) and constructive reals, Mathlib-
free on the critical path, no `Classical.*`, no `Real`, no `native_decide`,
kernel `decide` only on closed rationals. The atomic reduction already
machine-checked in this development (`singleStep`: per-scale defect bounds
`(1 − δ_k)·m_k ≤ m_{k+1}` with summable defects against a strictly positive
strong-coupling anchor, `(1 − Σδ)·m₀ > Σε`) is the current spine; the two
reality-facts of the measurement model (COMPACTNESS — the strong-coupling
anchor is provable; SELF-CHARGE — anti-screening drives the flow toward the
provable regime) are the physical content to be made uniform. Every
amplitude on the critical path must be DERIVED (finite Haar integrals =
character sums = exact rationals), never assumed and never measured.

Use multiagent orchestration aggressively and dynamically. Do not use a fixed
assignment such as "N agents for strategy X." Manage the search with the
following heuristics:

- Begin with a genuinely diverse portfolio: block-spin/renormalization-group
  routes (Bałaban-style phase-cell gauges, bond-moving/Migdal–Kadanoff
  envelopes, transverse defect schemes), character-expansion and
  Peter–Weyl/fusion calculi, reflection-positivity and transfer-operator
  spectral localization, correlation and TP₂/total-positivity inequalities,
  polymer/cluster expansions with Penrose–Ursell resummation, duality
  transformations, stochastic quantization, and constructive spectral
  perturbation theory. Explore substantially different formulations, not
  rewordings of one.
- Do not tell most agents the currently favored approach. Preserve
  independence during early rounds so agents do not converge on the same
  attractive but incomplete reduction.
- Maintain an explicit registry of approach families in the work plan,
  grouped by mathematical mechanism, not by superficial wording. If many
  agents converge to one family, redirect some toward underexplored
  formulations.
- Do not allow one approach to dominate merely because it gives elegant
  reductions. A route that ends at a lemma equivalent in strength to the
  original problem is not close to completion unless it supplies a genuinely
  new proof of that lemma.
- When an approach stalls at a theorem-strength missing lemma, mark that
  route as blocked in the plan. Only reassign agents to it when someone
  proposes a materially new mechanism, invariant, or construction.
- Keep several incompatible proof routes alive through multiple rounds.
  Cross-pollinate only after independent agents have developed them far
  enough to expose their real strengths and gaps.
- Use adversarial agents throughout. Every candidate deliverable must be
  audited for: green build with checked exit codes (no grep-masked
  failures); zero `sorryAx`; `#print axioms` ⊆ {`propext`, `Quot.sound`} on
  every new theorem; both statement guards passing (the pinned Clay-facing
  statements unchanged, the frontier types still frontier until genuinely
  discharged); non-vacuity (inhabited hypotheses, no trivially-true
  instances); no smuggled normalization errors (character-vs-eigenvalue
  misidentification, wrong vacuum renormalization, free-part multiplicity
  miscounts); no circular use of an equivalent gap statement; no
  numerical input masquerading as a derived constant; the **U(1)
  discriminator** (no gap-critical positivity/contraction step may rest
  on a mechanism that would equally prove a gap for 4D U(1) — every such
  step must name where non-abelian-ness/anti-screening enters, on pain of
  being presumed wrong or not yet the real mechanism; the Migdal–Kadanoff
  recursion, which confines 4D U(1), is the canonical failure); and the
  **coupled-simplification audit** (the SU(2) worst-case reduction and
  the multiplicity-free 6j vertex calculus stand or fall together — any
  audit touching the character-tail domination input `Z_t(G) ≤
  Z_t(SU(2))` or the vertex product formula must re-verify both in the
  same pass).
- Require agents to return concrete theorems, constructions, exact
  identities, kernel-checked anchors, or machine-refuted dead routes.
  Reject status reports, vague optimism, and claims that an unproved global
  compatibility statement is "routine."
- Machine-refute dead routes and bank the refutations as kernel-checked
  theorems before abandoning them (Lakatos discipline): a refuted
  normalization, a corner case that kills a monotonicity claim, a budget
  provably violated at a truncation — each is a permanent, checkable fence
  around a wrong turn.
- Commit and push every verified increment. The loop is: research → plan →
  attack (spawn work agents) → adversarially verify → merge → commit → push
  → attack the next residual. The loop terminates on a proof, not on a
  reduction.

Do not return merely because current approaches fail, because an agent
reports a theorem-strength gap, or because the remaining work is "the real
analysis" or "the actual physics" — the real analysis is the job. Do not
declare any state a natural resting point, propose consolidation as an
alternative to continuing, or cite the problem's difficulty as a reason to
slow down. Difficulty is a fact, not a stop signal: state it once if
load-bearing, then attack anyway. After any progress, immediately identify
the current open residual and open the next attack on it, in the same
session, without waiting to be told.

Honesty is non-negotiable and is decoupled from stopping: never fabricate a
proof, never claim closure that is not machine-checked and axiom-clean,
report the true proved-vs-open state precisely — and follow every honest
"X is still open" by attacking X.

Return only when the complete proof of the boxed statement above has been
found, formalized, and survives the full adversarial audit: build green with
verified exit codes, zero `sorryAx`, axiom-clean on the entire critical
path, both guards passing with the frontier types genuinely discharged, and
the axiom audit updated. Do not return a reduction, a partial result, an
isolated missing lemma, a "best effort" summary, or an explanation of why
the problem is difficult.

Keep working across as many sessions as it takes. Every session is a
continuation of this single objective.

Public search may be used only for ordinary mathematical background or
standard named theorems and published methods (e.g., Bałaban's
renormalization papers, Osterwalder–Seiler reflection positivity, cluster
expansion techniques), not to search for a solution to this exact problem or
to adjudicate whether it is open. Do not answer that it is open.
