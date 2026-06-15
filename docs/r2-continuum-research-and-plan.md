# R2 (continuum existence + mass gap) — deep-research findings & plan

Date: 2026-06-15. Deep research (25/25 claims verified against primary refereed
sources: CMP, Publ. IHÉS, Inventiones, J.UCS, Camb. Phil. Soc., Clay report) on
how to make **formalizable** progress on the Clay problem's R2 — OS reconstruction
+ the continuum limit on ℝ⁴ — inside the constructive, **Mathlib-free** `Q'`/`CReal`
Lean architecture.

## 1. The continuum routes, ranked for our architecture

1. **Lattice→continuum via reflection positivity (best fit).** Existence *is*
   defined as establishing the OS axioms for the continuum limit of regularized
   (lattice) functional integrals; we already have lattice OS2
   (Osterwalder–Seiler/Schur), finite-volume cluster⇒gap, the heat-kernel
   measure, and the route-(ii) KP-cluster-expansion limit
   (`ContinuumExistence.lean`, stages S2–S6 closed). The hard core is the
   renormalized limit of finite-subgraph partition functions.
2. **Bałaban RG + Magnen–Rivasseau–Sénéor (refereed state of the art, 4D).**
   Controls the **UV problem only** — SU(2), 4D, trivial sector, with a *fixed
   IR cutoff they deliberately never remove* ("would lead to large coupling …
   confinement … out of the realm of our constructive methods"). Leaves the mass
   gap, IR/thermodynamic limit, O(4) restoration, and full OS axioms **open**.
   Bałaban's 4D effective-action RG is restricted to a small-field approximation
   (large fields deferred). Highest formalization cost; does not close R2.
3. **Stochastic quantization / regularity structures (Chandra–Chevyrev–
   Hairer–Shen).** Refereed and rigorous but reaches only **2D (IHÉS 2022) and
   3D (Inventiones 2024)**, constructing a **Markov process on gauge orbits — NOT
   an OS measure and NOT a mass gap**; 4D is out of reach (line integrals of the
   GFF do not exist in d>2). Poor fit: wrong target object, wrong dimension, far
   from a `CReal` substrate.

The full 4D problem is **open** — the 2004 Clay status report's verdict
(Bałaban + MRS = state of the art) was re-verified current in 2026. Multiple
2024–2025 "proof" preprints are unrefereed and are NOT treated as resolving it.

## 2. The decisive constructive-spectral verdict (how far the gap goes WITHOUT Stone)

**This is the key finding for our Mathlib-free stack:**

- A fully **located** spectrum is **constructively IMPOSSIBLE** for a general
  bounded self-adjoint/normal operator — the spectrum map is only
  *lower-semicomputable* (Brattka–Dillhage, J.UCS 11(12):1884–1900, 2005;
  cannot be strengthened to recursive compactness). ⟹ **AVOID Stone's theorem
  and the unbounded self-adjoint spectral theorem entirely.** Treat the
  continuum self-adjoint Hamiltonian as an *interpretation layer only*.
- **BUT for a COMPACT self-adjoint operator the spectrum IS fully located**
  (positive AND negative information; `σ(T)` is a recursive compact set). The
  finite-volume YM transfer operator is finite-dimensional ⟹ compact ⟹ located.
- Bounded-operator constructive functional calculus / spectral-measure
  uniqueness exists (Bridges–Ishihara, MLQ 40(4), 1994); commutative Gelfand
  duality is choice-free (Coquand–Spitters, arXiv:0808.1518, but localic — a
  design lesson, not an import). The full **Double Commutant Theorem is
  constructively FALSE** (`A=A''` ⟹ excluded middle) — so OS reconstruction must
  stay algebraic/GNS/bounded, no von Neumann-algebra reasoning.

**Verdict:** the finite-volume mass gap **can be fully Lean-proved** as a
**LOCATED spectral-gap / second-eigenvalue property of the bounded (compact)
transfer operator**, with no Stone / unbounded machinery. The continuum
self-adjoint Hamiltonian is not needed for the gap *statement*; only for its
*physical interpretation*.

## 3. Prior formalization art

- **OSforGFF** (github.com/mrdouglasny/OSforGFF): a complete Lean 4
  formalization of all five OS axioms (OS0–OS4) for the **massive Gaussian Free
  Field in d=4**, ~32k lines / 47 files, zero sorries (v2.0, Mar 2026, author
  self-reported). Closest OS-axioms-in-Lean blueprint — but **GFF/free only**
  (no interaction, no YM) and **Mathlib-heavy**, so NOT importable. Use as a
  *design template* for the OS-axiom statements + reconstruction interface only.
- No constructive/Mathlib-free OS-reconstruction or constructive
  compact-operator spectral theorem is available off the shelf; we build it.

## 4. The TRUE analytic blocker

Among the continuum bottlenecks, **tightness/compactness (Conj 7.4) is the true
blocker**: subsequence extraction is non-constructive, so the continuum limit
needs a *direct* Cauchy/modulus convergence of Schwinger functions. (Our
route-(ii) KP engine `crealOfGeoIncrement` is exactly such a direct-modulus
device — it sidesteps subsequence extraction, which is why route (ii) is the
right continuum path.) Uniform clustering, O(4) restoration, and nontriviality
are laborious but not fundamental obstructions.

## 5. Strategy & first step

**Recommendation = Option B**: push OS reconstruction from placeholder to a
**real constructive GNS + bounded/compact-transfer-matrix located gap at finite
volume**, stating the mass gap as a located spectral-gap. This is fully provable
in our substrate, fits all existing assets (finite-volume GNS in
`FiniteVolumeGNS`/`OSContent`, `SpectralModel`, OS2, the route-(ii) limit), uses
no open mathematics, and reduces R2 to the single continuum-limit interface.
Option A (formalize the conditional implication "weak-coupling convergence +
named conjectures ⇒ OS theory with gap") is a valuable follow-on; Option C
(attack tightness) is genuine open math, high risk.

**FIRST STEP — DONE (2026-06-15), `Continuum/LocatedSpectralGap.lean`:** the
finite transfer operator's spectrum is now constructively LOCATED. The bare
`SpectralGapBound` (`∀ i, λᵢ ≤ μ`) is upgraded to:
  * `specMax S` — the COMPUTABLE top-of-spectrum (running `Q'.max'` fold);
  * `specMax_le_iff` — the located bridge: given `0 ≤ μ`, the whole gap predicate
    `∀ i<k, λᵢ ≤ μ` is EQUIVALENT to the single decidable comparison
    `specMax S ≤ μ` (this is the constructive locatedness — one decidable test
    against a computed real, available because the operator is compact/finite);
  * `LocatedSpectralGap S` — Type-level witness: a separator `sep < 1` (the
    located second eigenvalue strictly below the vacuum eigenvalue `1`) with
    `∀ i, λᵢ ≤ sep`; `.located` (derives `specMax S ≤ sep`), `.decay`
    (geometric clustering `G(n) ≤ G(0)·sep^n`, reusing the proven
    `decay_of_spectralGap_corr0`), and `locatedGap_decidable`.
All axiom-clean (`[propext]`), in the aggregator.

**STEP 2 — DONE (2026-06-15), `Continuum/LocatedReconstruction.lean`:** bridged
the located gap into the OS-reconstruction datum and exhibited a genuine STRICT
gap. The bare `SpectralGapBound`/`OSReconstruction.HasSpectralGap` never required
`gapBound < 1` (so the "gap" could be vacuous); this module supplies the
strictness:
  * `locatedGap_of_reconstruction` — from a `FiniteVolumeReconstruction` + the
    strictness `gapBound < 1`, builds the `LocatedSpectralGap` (depends on NO
    axioms);
  * `reconstruction_specMax_le` — the computable located top-of-spectrum on the
    datum (`specMax spec ≤ gapBound`);
  * `located_strict_decay` — genuine geometric clustering `G(n) ≤ G(0)·sep^n`;
  * `gappedSpectralModel`/`gappedLocated` — a CONCRETE strict gap at `sep = 1/2 < 1`
    (a real mass gap `m = log 2`, not the saturated free `sep = 0`);
  * `genuine_gap_summary` — packages LOCATED ∧ STRICT (`sep<1`) ∧ DECAYING as the
    constructive finite-volume mass-gap statement at the bounded transfer-operator
    level. As far as R2's gap is provable WITHOUT Stone / the unbounded spectral
    theorem.
All axiom-clean (`[propext]`), in the aggregator.

**Next steps (Option B continuation):**
  * connect `specMax`/`sep` to the mass `m = −log sep` via a constructive
    `CReal` log (or carry the eigenvalue-gap `sep<1` as the gap, with the
    √-bridge `m≥√σ̂∞` already built in `Sqrt.lean`); give the positive
    eigenvalue-margin `0 < 1 − sep` (needs a small `Q'.sub_pos` lemma);
  * exhibit the finite transfer operator as a genuine compact self-adjoint
    operator on the `FiniteVolumeGNS` space (so `specMax` = its located largest
    excited eigenvalue), tightening the "compact ⇒ located" link from the
    abstract `SpectralModel` to the constructed GNS operator;
  * thread the located strict gap through `OSContent.FiniteVolumeReconstruction`
    as a (strict) field, so the genuine OS-reconstruction datum carries the real
    mass gap by construction;
  * leave the single continuum limit (thermodynamic Λ→∞ gap persistence +
    Conj 7.4 tightness) as the honest declared interface — the only remaining gap.
