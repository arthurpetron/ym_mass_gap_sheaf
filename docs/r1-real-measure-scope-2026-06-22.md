# Scope: the R1 real-measure construction (the unified wall, 2026-06-22)

Target named in the consolidation (`abstract-tower-and-r1-wall-2026-06-22.md`): **construct the actual
4D SU(2) lattice gauge measure** and **connect the abstract structures** (`PolymerModel`, `corr`,
`animalCount`, the KP criterion's enumeration) **to it**. This is Clay R1 — the deepest wall, where
every route (matched-retune, cluster-expansion, continuum-oracle) bottoms out. Read-only scope; eyes
fully open. No code changed.

## What R1 actually requires (decomposition)

R1 splits into a CONSTRUCTIVE-FRIENDLY half and a HARD-ANALYSIS half. This is the key finding.

### Half 1 — the finite-volume real measure E_Λ (constructive-friendly)
The actual SU(2) lattice gauge functional on a finite box Λ: Haar integration over `SU(2)^{E_Λ}` of a
Wilson observable against the heat-kernel plaquette weight `∏_p K_w(U_∂p)`.

KEY INSIGHT (why this sidesteps the no-CReal-integration wall): Wilson observables and the heat-kernel
weight both expand in **characters**, and Haar integration of a product of characters is **character
orthogonality** — a DISCRETE (Kronecker-δ / Clebsch–Gordan) operation, already in the repo
(`fusionOK`/`Clebsch`, `WilsonFunctional.wilsonCharExp`, the Pivot Gram machinery). So the
finite-volume expectation `E_Λ[W]` is a FINITE rational/`CReal` character sum — NO continuous
integration needed. This is genuinely buildable.
- Status: single-edge done (`WilsonFunctional` E1); the box product + character-orthogonality
  contraction (E2 fusion, already have `fusionOK`/Clebsch) is the work. TRACTABLE.

### Half 2 — the three real connections (the wall)
1. **Kolmogorov consistency of the REAL family** `restrict_{Λ'⊂Λ} E_Λ = E_{Λ'}` — needs the
   heat-kernel **semigroup/convolution** property under edge-marginalization (E3 in the
   `WilsonFunctional` roadmap). `ObservableMeasure` proves the σ-additive coarsening for an ABSTRACT
   consistent family (`is_consistent ⇒ su2_continuum_measure`); the missing piece is proving the real
   Wilson family IS consistent. MEDIUM–HARD (the convolution identity is standard but unformalized).
2. **The polymer-expansion identity** `Z_Λ = ∑_{polymer configs} ∏ activity(X)` and the connected form
   `⟨W₀;Wₙ⟩_Λ = ∑_{X connecting 0,n} activity(X)` — the algebraic identity that makes `PolymerModel`/
   `animalCount`/the KP enumeration describe the REAL `E_Λ`. This is the **real-polymer reindexing**
   that the abstract KP criterion currently fakes (it sums over `animalCount`, not real configs).
   HARD: it's the Mayer/cluster expansion of the actual partition function — known mathematics
   (Friedli–Velenik Ch.5; Seiler LNP 159) but a substantial constructive formalization.
3. **`corr` ↔ the Wilson correlator** — the abstract `corr = Σ wᵢλᵢⁿ` (in `ClusteringImpliesGap`) must
   be the actual `⟨W₀;Wₙ⟩_c` of `E_Λ`, i.e. the spectral decomposition of the real transfer operator.
   Then `clustering_implies_located` applies to the REAL gap. HARD: requires the real transfer
   operator's spectral representation (the GNS construction exists abstractly in `FiniteVolumeGNS`,
   but its eigenvalues are inputs, not built from `E_Λ`).

The continuum limits (a→0 crossover = `TrueRGComparison`; O(4) restoration) sit ABOVE R1's Half-2 and
remain genuinely-open mathematics (per the prior scopes) — out of scope for a first R1 push.

## Honest cost / risk

| Piece | Status | Tractability |
|---|---|---|
| H1 finite-vol `E_Λ` (character-sum) | E1 done; box-product to build | TRACTABLE (discrete, no integration) |
| H2.1 real-family Kolmogorov consistency | abstract proved; real family unproved | MEDIUM (convolution identity) |
| H2.2 polymer-expansion identity | absent | HARD (real cluster expansion) |
| H2.3 corr↔correlator + real spectrum | GNS abstract; spectrum is input | HARD (real transfer-op spectrum) |
| continuum a→0, O(4) | open math | OUT OF SCOPE (genuinely open) |

The realistic, genuine, bankable advance is **H1 + H2.1**: a real finite-volume SU(2) expectation
functional (character-sum) that is provably Kolmogorov-consistent ⇒ a GENUINE inhabitant of
`ObservableMeasure.su2_continuum_measure` for the ACTUAL Wilson family (replacing the `trivSystem`
placeholder). That converts the inverse-limit existence from a placeholder to a real σ-additive
infinite-volume YM functional — a true R1 partial-construction, the first non-placeholder continuum
object in the repo. H2.2/H2.3 (the polymer identity + real spectrum) remain the hard wall and would be
subsequent waves; the continuum limit stays open.

## Recommendation

Commit to **Wave 1 = H1 + H2.1** (the real finite-volume character-sum functional + its
Kolmogorov-consistency ⇒ a genuine non-placeholder inhabitant of the inverse-limit). This is the
highest-leverage genuinely-tractable R1 step: it produces the first real continuum YM object and is
gated only on discrete character algebra already in the repo (no CReal integration, no open
mathematics). H2.2/H2.3 are the residual wall — scope them only after Wave 1 lands and we see the real
`E_Λ` in hand. The continuum a→0/O(4) limits stay honestly open.

Decision point for the user: launch Wave 1 (H1 + H2.1) as the next build, or hold here at the
consolidated summit.
