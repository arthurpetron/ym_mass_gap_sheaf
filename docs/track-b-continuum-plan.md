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
    cluster expansion.  PARTIAL: the *free* finite-volume rung
    (`Continuum/E2ProductFunctional.lean`, `prodFunctional` + the
    independence law); the plaquette-coupled rung
    (`Continuum/PlaquetteReweight.lean` — a constructive `Q'` reciprocal +
    the reweighting-positivity lemma `Eβ(o)=Ew(o)/Z` positive/normalized,
    with `Ew_pos` = OS2 as the isolated input); and the KP→limit ENGINE
    (`Continuum/KPLimit.lean` — `crealOfGeoIncrement`: a geometric increment
    bound `|S_{Λ+1}−S_Λ| ≤ C·ρ^Λ` gives a `CReal` limit with explicit
    modulus, the "second half" matching the proved `Z_t<1/16` smallness).
    OPEN: the actual lattice polymer expansion deriving the increment bound;
    plaquette weight `W=e^{−S}` with `Z>0`; OS2 itself.
  * **E3 — RG consistency (the load-bearing claim).**  Block-spin transport
    `restrict (E_{k+1}) (incl k) = E_k`.  PARTIAL
    (`Continuum/RGTransport.lean`): the transport lemma
    `consistent_iff_transport` (consistency ⟺ the value law `E∘map = E`); a
    NON-trivial consistent tower on genuine non-`PUnit` data (the SU(2)
    character algebra `charAlg` + diagonal heat-kernel functional `charFunc`,
    proved a `ProbFunctional` and genuinely non-constant), replacing the
    `trivConsistent` placeholder; and a non-identity block-spin *-hom
    (`collapseHom`) with proved consistency.  OPEN: the genuine SU(2)
    block-spin map (neither identity nor collapse), strict-`=` vs `.eqv` for
    a *moving* heat-kernel tower, and the QUANTITATIVE σ̂-budget transport /
    named conjectures (Conj. 7.4, O(4)).
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
    is grinding the `Q'` polynomial identity — SOLVED by the reflective
    `Q'` ring `Constructive/QPoly.lean` (`poly_eqv … (by decide)`).
  * **The 2×2 certificate — DONE** (`Continuum/Pivot2*.lean`): full
    heat-kernel PSD on degree-≤1 observables — `form2_nonneg : 0 ≤ E(a²)` for
    `a = c₀χ₀+c₁χ₁` and ALL real `c₀,c₁` (off-cone, beyond
    `coneExp_nonneg`).  Pivot `D₁ = 1+m₂−m₁² ≥ 0` (`pivotGram_nonneg`) from
    three pieces (developed in parallel): moments→polynomial (expNeg power
    law), the SOS factorization `1+3r⁴−4r³ = (1−r)²(3r²+2r+1)` via `QPoly`,
    and `(1−r)²(3r²+2r+1) ≥ 0`; then completing the square `form2 ≃
    (c₀+c₁m₁)² + D₁·c₁²` → `geRat_sos_creal`.  Each higher order `N×N`
    follows the SAME pattern (moments→poly, factor by `QPoly`/`decide`, SOS,
    Schur).
  * **The 3×3 certificate — DONE** (`Continuum/Pivot3*.lean`):
    `form3_nonneg : 0 ≤ E(a²)` for `a = c₀χ₀+c₁χ₁+c₂χ₂` and ALL real `cᵢ`.
    Division-free via scaling by `P = 3a⁴+2a²+1 ≥ 1`: `P·form3 ≃ P·M₀² +
    M₁² + big·M₂²` (a degree-32 identity discharged by `QPoly`/`decide`),
    then `form3 ≥ 0` by the pointwise `P ≥ 1`.
  * **The all-orders certificate** (uniform `D_s ≥ 0` for all `s`) — the
    irreducible moment-positivity content.  PARTIAL (`Continuum/Moment
    Positivity.lean`): the leading Gram minors factor UNIFORMLY as
    `Δ_N(a) = S_N(a)²·P_N(a)` with `P_N` a nonnegative-coefficient polynomial
    (so `Δ_N ≥ 0` with no per-N SOS search) — verified exact through N=6,
    proved end-to-end at N=3 (`delta3_nonneg_at`) with a reusable
    nonneg-coefficient positivity engine (`geRat_minor_factored`).  OPEN: the
    uniform N-indexed construction of `(S_N, P_N)` (most promising route: the
    Favard three-term recurrence `β_s(a) ≥ 0`), the moment-bridge per order,
    and the Sylvester `(∀N Δ_N≥0) ⇒ PSD` step.  Alternative: route (b)
    (Hermite/Poisson) makes positivity manifest but needs theta machinery.
    Favard progress (`Continuum/Favard.lean`): `β_s = Δ_s·Δ_{s−2}/Δ_{s−1}²`,
    so `β_s ≥ 0 ⟺ Δ_s·Δ_{s−2} = (S_s S_{s−2})²·(P_s P_{s−2}) ≥ 0` — proved
    for `s = 1..4` (incl. a degree-160 `decide` at `s=4`), with `P_N ≥ 1`
    (`geRat_ceval_ge_const`) and nonneg-coeff cone closure under `pmul`.  The
    remaining crux is *evenness of every cyclotomic multiplicity* in `Δ_N`
    (⇒ the perfect square `S_N²` uniformly).  SOLVED for the square factor
    (`Continuum/QHankel.lean`): the explicit q-product
    `S_N(a) = ∏_{j=1}^{N−1}(a^{2j}−1)^{N−j}` (Möbius-inverted from the
    cyclotomic table, sympy-verified through N=8) is realized uniformly
    (`def SN`), proved a perfect square `≥ 0` for ALL N
    (`geRat_SN_sq_nonneg`), with the uniform reduction `Δ_N = S_N²·P_N`,
    `P_N` nonneg-coeff ⇒ `Δ_N ≥ 0` (`geRat_minor_SN_factored`) and the
    telescoping recurrence `S_s·S_{s−2} = (a^{2(s−1)}−1)·S_{s−1}²`.  The
    moments are the SU(2)-theta (continuous q-Hermite, `q=a²`) deformation of
    the semicircle; `(2N−1)!!` is the q-Hermite Hankel signature.  OPEN
    reduces to a SINGLE statement: **`P_N = Δ_N/S_N²` has nonneg coefficients
    for every N** (exact through N=8; not yet N-indexed) — lever: the
    positive Favard factor `P_s P_{s−2}/P_{s−1}²`, or LGV/non-intersecting
    paths for the q-Hankel cofactor.  Plus the (bookkeeping) order-N
    moment-bridge and the Sylvester `(∀N Δ_N≥0) ⇒ PSD` step.
  * **E2 (cluster expansion / infinite volume)**, **E3 (RG transport)** —
    the analytic core, interleaved with B2's OS axioms.

The genuinely-open residue (named conjectures, the quantitative RG
transport) is flagged at E3; everything up to it is formalizable, and we
build toward it rather than around it.
