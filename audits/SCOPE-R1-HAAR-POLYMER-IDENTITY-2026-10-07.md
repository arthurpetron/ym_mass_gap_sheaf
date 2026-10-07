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

## PROVED: commit 10, `SU2LinkDecay.lean`

- `su2_link_decay` chains polyPartition_eq_Xi → link KP (commit 9) → chainW_bound (lattice decay).
- Constants: w₀=1e-8, ε_L=1e-15, η=1/2500, K=(5/3)^24 per plaquette, rate λ=6/7 per unit of distance, with weight 2|h|.
- Observable: insertion/removal correlation U only, not Wilson loops.
- Strong coupling, so it also holds for U(1): not gap evidence.

## PROVED: commit 11, `SU2LinkDecayHeat.lean`

- charEnv swap: w₀ = 1/100000, ε_H = 5e-15, K = (5/3)^24, η = 1/2500, λ = 6/7.  Uniform in M.
- Lever: sharpening K.  A rooted tree count on the 20-neighbour link graph (K ≈ e·20 ≈ 54) with a single factor of K in the decay could reach w ≈ 1/40.
- Strong coupling, heat-kernel (spin-truncated), not Wilson; also true for U(1), not gap evidence.

## PROVED: commit 12, `SU2ObsInsertion.lean`

- Observable insertion as modified activities on the same gas.  Cross-multiplied truncation identity.
- The decay and the part-2 (OS/transfer) map are in SCOPE-R1-CLUSTER-TO-GAP-2026-10-07.md.
- Strong coupling, heat-kernel (spin-truncated), not Wilson; also true for U(1), not gap evidence.

## PROVED: commit 13, `SU2ObsRoot.lean`

- c₀χ ≅ χ factorisation proved (not docs-only).  One-root decomposition.
- Open for the correlator bound: the two-root expansion and a chain bound for T(y,g)=Ξ(l)Ξ(l_yg)−Ξ(l_y)Ξ(l_g).  chain_bound cannot be reused with activity-1 roots, because KP fails at the roots.  The w_H modified activities are also open.
- Next big item: RP plus a transfer matrix for the torus polyPartition.

## PROVED: commit 14, `PolymerRemovalChain.lean`

- T(y,g) bound by D-telescoping started from the y and g neighbourhoods; no KP at the roots.
- Strong coupling, heat-kernel, U(1)-true.

## PROVED: commit 15, `SU2RemovalDecay.lean`

- Instances with K = (5/3)^24 and K = (3/2)^24, plus the SU(2) w₀ instance.
- OPEN: the two-root formula and the rooted sum.

## PROVED: commit 16, `SU2TwoRoot.lean`

- The exact two-root formula, using T(b,a) kernels and both-point polymers.

## PROVED: commit 17, `SU2ObsActivity.lean`

- The activity, rooted-sum, λ-shift and environment inputs for the correlator bound.

## PROVED: commit 18, `SU2PairKernel.lean`

- The pair-kernel bound.

## PROVED: commit 19, `SU2TruncDecay.lean`

- Truncated χ₁ correlator decay at w₀, uniform in N and M.
- OPEN: the Wilson analogue; ratio form (divide by Z²; Z > 0 is available from `env_w0`); the wH version.

## PROVED: commit 20, `SU2TruncRatio.lean`

- The ratio form.

## PROVED: commit 21, `SU2TruncGeneric.lean`

- The generic correlator decay.

## PROVED: commit 22, `SU2WilsonObsActivity.lean`

- The observable Wilson activity bound, uniform in K.

## PROVED: commit 23, `SU2WilsonTrunc.lean`

- The Wilson truncated-correlator ratio bound at β_S.

## SCOPE: commit 24, transfer matrix

- See `docs/SCOPE-SU2-TORUS-TRANSFER-MATRIX-2026-10-07.md`.
