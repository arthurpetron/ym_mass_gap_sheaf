# Scope: width-uniform strong-coupling polymer/KP route (2026-10-07)

Label: GROUP-BLIND PLUMBING.  Under the U(1) rule, strong-coupling KP holds for U(1) too, so
this is not gap evidence on its own.  It targets the failure recorded in
SCOPE-MIXRATE-MARGIN-SCALING: the per-face Doeblin margin is ≤ 2^{-15 width³}.

## What the repo already has (reused, not duplicated)

- `PolymerModel`: `Lattice`, `Polymer`, connectivity, the Haar link constraint
  (`fusesToTrivial_iff_eq`), and the activity ζ(X) = Π coeffW, which is nonnegative.
- `KPCriterion`: `activity_single_rep` (a connected polymer carries one rep) and the KP criterion
  `kp_criterion_of_count`, CONDITIONAL on a `ClusterCountBound`.
- `BddLatticeAnimal` / `GenuineKP`: the genuine lattice-animal count `animalCount n ≤ ((D+1)²)^n`,
  i.e. the repo's ball/animal count, instantiated on `zChain` (a 1-D chain, D = 3, K = 16), with
  `kpRatio = 96 w³ ≤ 1/2` at w = 1/6.
- `AbstractPolymerXi`: the hard-core Ξ over `List Plaquette` with NONNEGATIVE activities.
  - `Xi_cons_split`, `Z_step_ratio` (Ξ(γ::Λ) ≤ Ξ(Λ)(1+ζγ)) and `Xi_le_prod_one_plus`.
  - The named open item there is `AbstractRealPartitionIdentity`, the abstract↔real Haar
    reorganization (R1 wall).
- Also present: `MayerClustering`, `MayerUrsellZ4*`, `Penrose*`, `Ursell*` (Mayer/Ursell
  pieces, mostly zChain or pinned), `ClusterGapReduction` (`UniformClusterBound` ⇒ continuum
  rate, a conditional bridge), `ClusteringImpliesGap`, and `KPLimit` / `KPIncrement`
  (geometric-increment infinite-volume limits).
- Z4 geometry: `Z4HalfTimeReflection*`, `ClusterCount4DProgress`, and the slab carriers.
  There is NO genuine 4D animal count instantiated at Z4 plaquettes: `ClusterCount4DProgress`
  is progress only.

## Gap identified

With nonnegative activities, Ξ ≥ 1 is trivial and the KP lower bound carries no content. The
content of KP lies in SIGNED or complex activities: truncated correlations, and
characters-minus-mean expansions. The repo has no signed finite KP lemma.

## Minimal constructive statement (DONE: `SignedPolymerKP`, PROVED)

Abstract finite polymer system: a type α, signed z, and a symmetric incompatibility `inc`, with
Ξ[] = 1 and Ξ(a::l) = Ξ(l) + z_a·Ξ(l ∖ N(a)).  Assume
- |z| ≤ ε;
- each list has ≤ D elements incompatible with any a (`DegOK`);
- M ≥ 1, Mε·M^D ≤ M−1, and εM^D ≤ 1.

Then for every finite Λ:
- `kp_main`: Ξ(Λ) ≥ 0, and the removal ratio Ξ(Λ∖γ) ≤ M·Ξ(Λ) for every γ ∈ Λ, at any position.
- `kp_filter`: Ξ(Λ.filter q) ≤ M^{#removed}·Ξ(Λ).
- `kp_lower`: 1 ≤ M^{|Λ|}·Ξ(Λ).
- `kp_upper`: Ξ(Λ) ≤ (1+εM^D)^{|Λ|}.

So −|Λ| log M ≤ log Ξ ≤ |Λ| log(1+εM^D), with constants depending only on (ε, D). This is
the ratio form. It needs no logarithm, and Ξ is permutation-invariant (`Xi_swap`, `Xi_front`).

Example: D = 24, M = 2 needs ε·2^{24} ≤ 1/2, i.e. ε ≤ 2^{-25}.

## Next (OPEN)

1. Size-weighted KP, where polymers have unbounded degree. The hypothesis becomes
   Σ_{γ'≁γ}|z(γ')|·a(γ') ≤ log-free a(γ)-type weights. This is needed for real polymers
   (lattice animals of all sizes).
2. Decay of truncated correlations: Ξ(Λ)Ξ(Λ∖(N(A)∪N(B))) − Ξ(Λ∖N(A))Ξ(Λ∖N(B)) is bounded
   by a sum over chains from A to B, each contributing ≤ (εM^D)^{dist}.
3. Identifying the activities with the repo's slab expansion: the R1 wall, plus a genuine
   Z4 animal count.
4. Feeding the result into a width-uniform transfer margin, via a clustering ⇒ gap bridge
   (`ClusteringImpliesGap`, `ClusterGapReduction`).

## Update (2026-10-07): items 2 and 3

- **Item 2 (decay), partial.** `SignedPolymerDecoupling`:
  - `Xi_append_decoupled`: if Λ₁ and Λ₂ are mutually compatible, then Ξ(Λ₁++Λ₂) ≈ Ξ(Λ₁)Ξ(Λ₂).
  - `truncated_zero_of_decoupled`: Ξ(Λ∖A∖B)Ξ(Λ) ≈ Ξ(Λ∖A)Ξ(Λ∖B) when A touches only Λ₁ and
    B touches only Λ₂.
  - This is clustering at d = ∞ only.
  - Still OPEN: the finite-d bound C(εM^D)^d.
    - Head-peeling does not close on the truncated quantity. With c ∉ A∪B, the expansion is
      Δ(c::l) = Δ(l) + z_c·[mixed cross terms] + z_c²·Δ(l∖N(c)), and the cross terms are not
      of Δ form.
    - Plan: either a ratio-Lipschitz induction (R_A = Ξ(Λ∖A)/Ξ(Λ) telescoped as products of
      1/(1+z_c R_{N(c)}), with Lipschitz constant ≤ M², giving δ_d ≤ (D ε M²)·δ_{d−1}), or a
      replica (doubled-gas) swap argument.
- **Item 3 (Z4 animal count): already in the repo, no new code.**
  - `ClusterCount4DProgress.z4Chain` is a genuine BddLattice on Z≥0⁴ plaquettes (corner-anchored
    box, not a torus), with degree D = 24 (`z4Nbrs_length`, `z4_sound`).
  - `z4ClusterCountBound` gives animalCount n ≤ 625^n (K = (D+1)²).
  - `z4ClusterCountBound_animal` carries the unconditional overcount via `AdjSpanningBuild`.
  - The torus version is not instantiated.
  - Linking this count to `SignedPolymerKP` needs the size-weighted KP (item 1), because the
    polymer incompatibility degree is unbounded.

## Update (2026-10-07): size-weighted KP (`SizeWeightedPolymerKP`)

- **Generic weighted KP (PROVED).** Weights m ≥ 1 and |z| ≤ e, with the Dobrushin condition
  `Cond`: m_a·e_a·Π_{x∈Λ,x≁a} m_x ≤ m_a − 1, plus `Cond2`: e_a·Π ≤ 1.  Both are hypotheses over
  the finite Λ, so there is no unbounded sum.
  - `kpw_main`: Ξ ≥ 0 and Ξ(Λ∖b) ≤ m_b·Ξ(Λ).
  - `kpw_filter`: Ξ(Λ.filter q) ≤ Π_{removed} m·Ξ(Λ).
  - `kpw_lower`: 1 ≤ Π m·Ξ.
  - The degree may be unbounded.
- **Exp-free product-to-sum (PROVED).** `prod_le_sum`: Π(1+δ) ≤ 1+2Σδ when 2Σδ ≤ 1.
- **Z4 numbers (PROVED).** ε = 1/10000, so |z(γ)| ≤ ε^{|γ|}; m(γ) = 1 + η^{|γ|} with
  η = 1/2500.
  - 625η = 1/4, and `geom_quarter` gives Σ_{n=1}^N (1/4)^n ≤ 1/3 for every N (finite closed form).
  - `z4_cond`: Cond and Cond2 hold PROVIDED `hgroup`: Π_{x≁a}(1+η^{|x|}) ≤ (5/3)^{|a|}.
  - The scalar check is `z4_scalar`: (1+η^k)·ε^k·(5/3)^k ≤ η^k for k ≥ 1.
- **What remains for `hgroup` (OPEN):**
  1. Grouping: Π_{x≁a}(1+δx) ≤ Π_{p∈a}(1 + 2Σ_{x∋p}δx). Assign each incompatible x to a
     shared plaquette of a, then apply `prod_le_sum` per plaquette.
  2. Per-plaquette sum: Σ_{x∈Λ, x∋p} η^{|x|} ≤ Σ_n 625^n η^n ≤ 1/3. This needs Λ's polymers
     through p of size n to be duplicate-free and to inject into
     `BddLatticeAnimal.enumPolys z4Chain p n`, whose length is ≤ 625^n
     (`z4ClusterCountBound_animal`).
  - With (1) and (2), 1 + 2·(1/3) = 5/3, which closes `hgroup`.
- **Ratio-Lipschitz decay:** NEXT; not started.

## Update (2026-10-07): `hgroup` closed, Z4 KP unconditional (`Z4PolymerKP`)

- **Polymer.** A `Z4BoxGas` is a finite list of plaquette sets on `z4Chain` (the
  corner-anchored Z≥0⁴ plaquettes) with these properties:
  - each set is duplicate-free and internally connected (a genuine lattice animal);
  - 1 ≤ |X| ≤ N;
  - supports are pairwise distinct.
  - Incompatibility `shareB` means sharing a plaquette.
- **Hypothesis-free main result.** `z4_kp` holds for every such list and every activity with
  |z X| ≤ (1/10000)^{|X|}:
  - Ξ ≥ 0;
  - Ξ(Λ∖b) ≤ (1+(1/2500)^{|b|})·Ξ(Λ);
  - 1 ≤ Π(1+(1/2500)^{|X|})·Ξ(Λ).
- **Ingredients:**
  - `group_le`: the grouping lemma, using the computable first-shared-plaquette choice `asg`.
  - `pigeon`: the up-to-support pigeonhole.
  - `class_sum`: the per-plaquette sum ≤ geoS N ≤ 1/3, via `z4ClusterCountBound_animal` (625^n).
  - `z4_hgroup`.
  - Two `simpa`/`omega` uses that pulled in `Classical.choice` were replaced by explicit Nat
    lemmas.
- **Decay:** the ratio-Lipschitz decay is NEXT; not started.
