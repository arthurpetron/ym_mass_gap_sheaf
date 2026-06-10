# Track B — Continuum YM theory in Lean: roadmap to existence

Track B builds the continuum SU(2) (then SU(N)) Yang–Mills theory in Lean:
the continuum measure/state `μ_∞`, the OS axioms, OS reconstruction to a
Hilbert space + self-adjoint Hamiltonian, and the spectral gap.  Its
load-bearing piece is **continuum existence**.  This file tracks the path
there so it stays a live goal, not a permanent input hypothesis.

## 0. The honest target

The full rigor of 4D YM continuum existence is open in the mathematics
literature (it *is* the Clay existence problem).  The project's thesis is
that its σ̂-trajectory framework constructs the continuum limit *in the
convergent (weak-coupling) regime*, modulo named conjectures.  "Getting
there" means formalizing that construction, with the named conjectures
(`sheaf-framework.tex` Conj. 7.4 tightness; O(4)-restoration) as the
honest open residue we flag explicitly.

## 1. Existence in the functional (Schwinger) picture — what's DONE

We represent `μ_k = Prob(SU(2)^{E_k})` by its gauge-invariant observable
expectations: `ProbFunctional` (positive, normalized `E : Obs → Q'`), the
Riesz/moment representation (`Continuum/ObservableMeasure.lean`, B1).  The
inverse-limit construction (`Continuum/ContinuumMeasure.lean`, B1) proves:

  * **given a consistent family of Wilson functionals, `μ_∞` exists** — the
    coherent functional on `colim Obs_k` (the inverse-limit thread);
  * `π_k(μ_∞) = μ_k` (the Daniell–Kolmogorov projection law) — proved,
    axiom-free;
  * `expectation_stable` — an exact per-observable modulus.

For OS reconstruction the **state** (Schwinger functional) is the needed
object; the σ-additive point-set measure is a Riesz refinement off the OS
critical path.  Hence:

> **Continuum existence = construct the actual *consistent* Wilson family.**

## 2. The path to the consistent Wilson family (the real analysis)

  * **E1 — single-scale finite-volume Wilson expectations.**  Gauge-invariant
    (Wilson-loop / character) expectations under the heat-kernel lattice
    measure, computed by Peter–Weyl / character orthogonality — rational for
    SU(2)/SU(3).  Connects to `RepTheory` + the A1 character machinery.
    *Formalizable; the genuine down-payment.*  Replaces `trivFunc` with the
    real finite-volume Wilson functional.
  * **E2 — thermodynamic (infinite-volume) limit.**  Infinite-volume
    expectations exist in the convergent regime via the Kotecký–Preiss
    cluster expansion.  The repo already has the KP framework
    (`Sheaf/Summability`, the KP certificates); lifting it to infinite-volume
    functional values with bounds is substantial but structured.
  * **E3 — RG consistency (the load-bearing claim).**  Block-spin transport
    `restrict (E_{k+1}) (incl k) = E_k`.  This is the project's
    inductive-step / `[P2.1]` content — currently Lean carries only the
    *shape* (the identity / zero-budget witness in `RG/BlockSpin`), with the
    quantitative transport in `computations/` (the σ̂ numerics).  Formalizing
    the genuine transport is the hardest core; parts (Conj. 7.4, O(4)) are
    flagged as conjectures in the paper.
  * **E4 — non-triviality.**  σ̂_∞ > 0 (Track A) ⇒ the continuum limit is
    non-trivial (a mass gap, not a free/trivial theory).  Track A's
    character-tail / σ̂ work plugs in here.

## 3. Interleaving with B2–B5 (so existence is not deferred)

**Principle:** replace the trivial/parametric functional with the *actual*
Wilson functional incrementally, so the OS axioms (B2) are propositions
about a **constructed** object, not about an abstract hypothesis.

  * **B2 (OS0–OS4)** reads off the functional directly: OS2 reflection
    positivity = positivity of `E` at reflected observables (`0 ≤ E(θ(a)*·a)`);
    OS1 = invariance under the symmetry `ObsHom`s; OS3 = symmetry of the
    Schwinger functions; OS4 = clustering at rate σ̂_∞ (Track A).  Build each
    for the constructed Wilson functional as E1–E3 land.
  * **B3** GNS reconstruction from the (reflection-positive) state → `H_phys`,
    contraction semigroup, self-adjoint `H ≥ 0` (needs a constructive
    operator/spectral layer — the largest undertaking).
  * **B4** cluster ⇒ gap (`σ(H) ∩ (0,√σ̂_∞) = ∅`); **B5** the √-bridge.

## 4. Status / next

  * **B1 framework** — DONE (inverse limit; `ProbFunctional`; coarsening
    preserves probability; limit + exact modulus; concrete inhabitant).
  * **E1 (real Wilson functional via characters)** — STARTED
    (`Continuum/WilsonFunctional.lean`).  `wilsonCharExp t s =
    dim(s)·e^{−t·C₂(s)}` is the genuine single-edge SU(2) heat-kernel
    character moment `⟨χ_{s/2}⟩_t` (Peter–Weyl orthogonality), reusing the
    A1 `expNeg` + the SU(2) Casimir.  Proved: each moment `≥ 0`
    (`wilsonCharExp_nonneg`) and `⟨1⟩_t = 1` (`wilsonCharExp_unit`, both
    bounds) — the genuine probability normalization.  Replaces `trivFunc`'s
    values with real heat-kernel expectations.
    *Remaining for E1:* full positivity `0 ≤ E(a*·a)` (heat-kernel Gram
    PSD) ⇒ a full `ProbFunctional`; then the plaquette-coupled finite
    lattice.
  * **E2 (cluster expansion / infinite volume)**, **E3 (RG transport)** —
    the analytic core, interleaved with B2's OS axioms.

The genuinely-open residue (named conjectures, the quantitative RG
transport) is flagged at E3; everything up to it is formalizable, and we
build toward it rather than around it.
