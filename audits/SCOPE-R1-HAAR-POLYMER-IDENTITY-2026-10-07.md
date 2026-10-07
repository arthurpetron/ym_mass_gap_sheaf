# SCOPE: R1, the Haar character expansion as a polymer gas (box, Dirichlet)

## PROVED: commit 1, `SU2HaarDisjointSupport.lean`

- `haar_disj n A p q`: if p is free off the block set A and q is free on A, then
  `quaternionHaar n (polyMul p q) ≈ quaternionHaar n p · quaternionHaar n q`.
- `mono_disj` is the monomial core.  It is built from `prefix_congr` / `exponentAt_drop` and
  needs no block swaps.  So the pointwise conjShear-equals-substitution lemma is **not needed**
  for R1 factorization.

## Remaining steps (not started)

1. **Support.** `plaqCharacter links N p s` has every monomial free outside the blocks
   `idxOf` of p's 4 links.  This needs support tracking through `PolyQuaternion.mul/conj`,
   `.scalar` and `characterPolynomial`.
2. **Expansion.**
   - `plaqWeight = c₀χ₀ + f_p`, where `c₀χ₀ ≈ 1` under Haar (`coeffW_zero_eqv`) and
     `f_p = Σ_{1≤s≤M} coeffW·χ_s`.
   - Then `∫Π(1+f_p) = Σ_{S⊆P} ∫Π_{p∈S} f_p`.
   - Grouping S into link-connected components and applying `haar_disj` gives a polymer sum.
3. **Activity bound.** `|z(γ)| ≤ (env)^{|γ|}`.

## MISMATCH 1: compatibility

- The existing KP and decay gas (`Z4PolymerKP`, `PolymerDecayZ4`, `PolymerLatticeDecay`) uses
  `shareB` = **shares a plaquette**.
- Haar factorization needs **link-disjointness**.  Two plaquette-disjoint polymers that share a
  link do not factorize.
- The correct gas has polymers that are link-connected (`connectedIn` is already link-adjacency).
  X and Y are incompatible iff some plaquette of X is equal or link-adjacent to one of Y, i.e.
  `q ∈ nbrs p` or `q = p`.
- **Consequence for the KP constants:**
  - The grouping lemma must run over the ≤ 25|a| plaquettes adjacent to a, not just the |a|
    plaquettes of a.
  - The `M` factor becomes about `(5/3)^{25|a|}` instead of `(5/3)^{|a|}`.
  - So ε = 1/10000 and η = 1/2500 no longer close the bound.  They must be re-derived, roughly
    ε ≲ η·(3/5)^{50}, which needs a much smaller w.
- `PolymerChainDecay`, `chainW_bound` and `diam_le` are generic in `inc` and carry over.
  `z4_hgroup`, `CS_le` and `CSW_le` must be redone for the new `inc`.

## MISMATCH 2: activity bound needs a new ingredient

- Only `multiLinkHaar_square_nonneg` (positivity on squares) is available.
- `|∫F| ≤ sup|F|` needs Haar positivity on polynomials that are pointwise nonnegative on
  `(S³)ⁿ`, or an SOS certificate for `(s+1)² − χ_s²` modulo the sphere ideal.  Neither is in
  the tree.
- Honest alternative: the ℓ¹ route `|∫F| ≤ Σ|coeff|·|moment| ≤ ‖F‖₁`.  This needs the new lemma
  `|sphereMoment4| ≤ 1`.
  - But `‖χ_s(U_p)‖₁` grows like ~(2·64)^s, so the activity bound would hold only for smaller w
    (about w ≤ 1/100), not at w = 1/40.
  - `charEnv` assumed `|χ_s| ≤ s+1` pointwise.  Under the Haar functional that is a sup bound,
    and it is exactly the missing positivity.

## PROVED: commit 2, `SU2HaarL1Activity.lean` (ℓ¹ route, decision (b))

- |sphereMoment4| ≤ 1 is proved as a Nat inequality on double factorials.
- `|∫_n p| ≤ ‖p‖₁`.
- `‖χ_s(U_p)‖₁ ≤ 513^s`.
- At **w₀ = 1/10⁸**: `‖Σ_{s=1}^M coeffW w₀ s χ_s(U_p)‖₁ ≤ ε_L = 1/10¹⁵` uniformly in M (via `charEnv_inv` at 513·w₀).
- `activity_bound`: `|∫ Π_{p∈γ} f_p| ≤ ε_L^{|γ|}`.

**Loss.** `term_le` bounds 513^s by 513^{s(s+2)}, an extra factor 513² at s = 1.  The pass is therefore not sharp; the sharp ℓ¹ threshold is about 25× larger in w.

No fail statement is given: the ℓ¹ envelope is an upper bound, not the true activity, so a fail would not certify anything about Haar.

## PROVED: commit 3, `SU2PlaqSupport.lean`

- Supports: `f_p` lives on the blocks `idxOf` of p's 4 links (`plaqLinks`).
- `polymer_factor`: `∫ (Π_γ F)(Π_R G) ≈ ∫Π_γ F · ∫Π_R G` when the block sets are disjoint.
- `idx_disj`: plaquettes sharing no link, with all links in `links`, have disjoint block sets.
- `plaqWeight_split`: `plaqWeight w M p = [([], coeffW w 0·1)] ++ fPoly w p M`.

## PROVED: commit 4, `SU2HaarAlgebra.lean`

- Context-stable equivalence `PE` (shifted moment functional `phi`).
- Proved: commutativity, associativity, unit, scalar≈1, closure under ·/++, and the factor-extraction `pe_extract`.
- No new hypotheses.

## PROVED: commit 5, `SU2ClusterExplore.lean`

- `explore_haar` and `root_step` (analytic half).
- Next, combinatorial half: leaves have R = P'.filter(¬touch A'); exploration commutes with filtering by a compatibility predicate; then Ξ identity by strong induction.

## PROVED: commit 6, `SU2PolymerIdentity.lean`. The identity is CLOSED.

- `polyPartition_eq_Xi` (finite box; hypothesis `Lk`: plaquette links are box coordinates).
- Remaining for R1: KP convergence for this gas at the link-incompatibility constants (grouping bound over `incL`).

## PROVED: commit 7, `SU2LinkGasGeometry.lean`

- Adjacency symmetry, the 24-neighbour cover `nb`, Adjacent from adj, and grown ⇒ connected.

## PROVED: commit 8, `SU2LinkGasBox.lean`

- `linkBox` and `hgroupL` (K = (5/3)^{24}).
- Note: the earlier shareB KP/decay results (PolymerDecayZ4, PolymerLatticeDecay) are for the *envelope* gas with shareB incompatibility. They are not a statement about the Haar measure. The Haar-faithful gas is gas N P with incL.

## PROVED: commit 9, `SU2LinkKP.lean`

- KP environment for (gas N P, incL), with the activity as a hypothesis so that both the ℓ¹ bound and Realizer's charEnv bound can feed it.
- Pass: ε_L=1e-15. K=(5/3)^24, η=1/2500.
