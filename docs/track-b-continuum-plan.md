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
    *Positivity (in progress):* the Gram entries `G_{μν} = ⟨χ_μ χ_ν⟩_t`
    are each `≥ 0` (`gramEntry_nonneg`, via the SU(2) Clebsch–Gordan
    decomposition + nonneg moments), giving **positivity on the
    nonnegative-coefficient cone** (`coneExp_nonneg`) — a genuine partial
    GNS positivity (substrate: `geRat_add`, `geRat_csum_nonneg`).
    *Remaining for E1:* FULL positivity (arbitrary real coeffs) = the
    heat-kernel Gram **PSD** theorem ⇒ a full `ProbFunctional`; then the
    plaquette-coupled finite lattice.  See the PSD subproject below.

### The heat-kernel Gram PSD theorem (E1's analytic completion)

No reusable proof exists (Mathlib is banned and classical; no portable
constructive compact-group heat-kernel positivity — the fact is nontrivial
even classically, since the SU(2)/S³ theta formula has mixed-sign Poisson
terms).  So we build it.  The irreducible content is *the heat-kernel
measure is positive* (≡ `E(a²) ≥ 0` for all `a` ≡ the Gram matrix
`G_{μν} = ⟨χ_μ χ_ν⟩_t` is PSD ≡ the moments are a genuine moment sequence).

  * **SOS backbone — DONE** (`Constructive/SumOfSquares.lean`): the reusable
    certificate consumer `geRat_sos : 0 ≤ Σ_{k<m} D_k·(L_k)²` for `D_k ≥ 0`,
    on the atoms `q_mul_self_nonneg`, `geRat_sq_nonneg` (a `CReal` square is
    `≥ 0`, immediate as `CReal.mul` is unclamped), `geRat_csum_nonneg`.
    This is what OS2 / OS4 / GNS positivity all consume.
  * **Route (a) — findings (in progress).**  Substituting `a = e^{−t/4}`
    makes the moments **polynomial**: `m_s = (s+1)·a^{s(s+2)}` (`m_1=2a³`,
    `m_2=3a⁸`).  Completing the square reduces `n×n` PSD to `n` pivots fed
    to `geRat_sos`; each pivot is a univariate polynomial in `a`, nonneg on
    `[0,1]`, with an SOS factorization.  The `2×2` pivot is
    `1+3a⁸−4a⁶ = (1−a²)²·(3a⁴+2a²+1) ≥ 0` — a clean, manifest certificate.
  * **The substrate wall (now mapped).**  `Q'` has ring-eqv lemmas but
    `CReal` has none (no `ring`), so each per-order certificate is a `CReal`
    polynomial identity.  Enabler landed: `SumOfSquares.Equiv_of_approx_eqv`
    reduces any `CReal` identity to a pointwise `Q'` identity, and
    `geRat_sos_creal` handles `CReal`-valued pivots.  What remains per order
    is grinding the `Q'` polynomial identity by hand (no `Q'` `ring`
    either) — mechanical but laborious — OR building a minimal `Q'`
    polynomial-normalization helper (the high-leverage next step, since
    route (a) needs it at every order).
  * **The all-orders certificate** (uniform `D_s ≥ 0` for all `s`) is the
    irreducible moment-positivity content; route (a) localizes but does not
    dissolve it.  Per-truncation it is finite; a uniform inductive proof is
    the open piece.  Alternative: route (b) (Hermite unfolding via Poisson
    summation) makes positivity manifest but needs theta-function machinery.
  * **E2 (cluster expansion / infinite volume)**, **E3 (RG transport)** —
    the analytic core, interleaved with B2's OS axioms.

The genuinely-open residue (named conjectures, the quantitative RG
transport) is flagged at E3; everything up to it is formalizable, and we
build toward it rather than around it.
