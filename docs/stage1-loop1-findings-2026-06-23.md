# Stage-1 Loop 1 — findings & frontier advance (2026-06-23)

Goal (fixed): Clay requirements, intuitionistically. Loop 1 attacked Stage 1 (fixed-spacing infinite-volume
gap, KNOWN math). Outcome: genuine frontier advance + the two crux residuals sharply isolated. Axiom-clean;
audit 2646 → 2686.

## What advanced (PROVED this loop)

WALL 1 — all-order Gram PSD:
- `FavardUniform.SN_telescope_gen` — the N-indexed cyclotomic recurrence `S_{k+1}·S_{k−1} = (a^{2k}−1)·S_k²`
  PROVED BY INDUCTION for ALL k (previously only k≤5 by `decide`; those are now corollaries). This is the
  structural backbone of the uniform factorization.
- `FavardUniform.uniform_PN_of_PNStep` — uniform `nonnegCoeffs P_N` (all N) REDUCED to a single named step
  `PNStep`; the exact obstruction PINNED: the cyclotomic factor `a^{2k}−1` has constant coefficient −1, so it
  leaves the nonneg-coefficient cone (`nonnegCoeffs_pmul` needs both factors nonneg). The uniform P_N wall is
  now ONE precisely-located inductive step.
- `CyclotomicPositivity` — positivity atoms (`0<q<1 ⇒ 0<1−q^n`; even powers ≥0) + minor-level `Δ_N ≥ 0`
  EXTENDED from N≤3 to **N≤5**. The Sylvester minor→form bridge is the named bookkeeping residual.

WALL 2 — Mayer / real correlator:
- `WilsonConnCorr.wilsonG` — the REAL Wilson connected 2-point correlator as a genuine character DOUBLE-SUM
  (de-fakes the trivial `WilsonCorrelator.wilsonCorr := corr (...)`/`eqv_refl`). `wilsonG_collapse` (single-rep
  collapse) + `wilsonG_decay` (GEOMETRIC DECAY ρ = 2w³ < 1 PROVED for the single-line geometry).
- `PinnedCluster` — `activity_le_leading` (coeffW w 1 = 2w³ dominates), `connected_spanning_size_ge` (new
  combinatorial lemma; `SepLattice` graph metric), `pinnedClusterTail` (geometric KP tail, ρ<1 at deg²w³≤1/12).

## The two crux residuals (Loop 2+ targets)

1. **`PNStep`** (Wall 1): the inductive step `nonnegCoeffs P_k ∧ nonnegCoeffs P_{k+1} ⇒ nonnegCoeffs P_{k+2}`.
   Blocked because the recurrence multiplies by `a^{2k}−1` (constant coeff −1). ATTACK NEXT: the cyclotomic
   structure — `a^{2k}−1 = ∏ Φ_d(a)` and the research's finding that `Φ_1=(a−1)` appears only to EVEN powers
   in the pivots; so the right object may be a reorganized `P_N` where the negative-constant factor is paired
   with another to stay in the cone (the LDLᵀ pivot is positive even though the naive product is not). Route:
   prove pivot-positivity via the cyclotomic-factored form rather than raw `nonnegCoeffs` of the product.
2. **`Z_step_ratio`** (Wall 2, Dobrushin): `Ξ_{Λ∪p} ≤ Ξ_Λ·(1 + w(p))` for arbitrary Λ — generalize
   `Z2_collapse` to the multi-plaquette link integral. ATTACK NEXT: the inductive add-one-plaquette ratio
   (Fialho 2001.00652), reusing `single-rep collapse` + `pinnedClusterTail`; then `wilsonG_eq_pinnedCluster`
   (the genuine `matches_abstract`) follows, deriving `sep` and feeding the existing positive-mass capstone.

## Loop 2 plan (next iteration of a→…→h)
(a) research the cyclotomic-pivot route for `PNStep` + the Dobrushin add-one-plaquette ratio specifics;
(b/c) plan; (d) parallel agents: [W1] the cyclotomic-factored pivot positivity (attack `PNStep`), [W2a]
`Z_step_ratio` Dobrushin induction, [W2b] wire `wilsonG` into a genuine `RealCorrelatorLink` for the
single-line geometry (de-fake the existing trivial link, deriving `sep` from ρ=2w³); (e) merge; (f) document;
(g) Lean; (h) repeat. The loop continues until Stage 1 is a complete fixed-spacing infinite-volume gap.
