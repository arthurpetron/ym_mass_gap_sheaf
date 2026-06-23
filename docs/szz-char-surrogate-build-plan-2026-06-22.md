# Build plan: the fixed-spacing SZZ character-surrogate (into waves, 2026-06-22)
**STATUS:** Scope/plan dated 2026-06-22; see the canonical ledgers for the outcome (docs/where-the-wall-sits-2026-06-22.md, docs/stage1-completion-ledger-2026-06-22.md, docs/stage2-progress-ledger-2026-06-22.md, docs/continuum-wall-outstanding-2026-06-22.md).
**CORRECTION:** This plan was ABORTED at Wave 3 — see docs/szz-surrogate-correction-2026-06-23.md (the Wave-2/3 interacting chain is inadequate; the named obligation is unsatisfiable at strong coupling).

Goal: a NON-VACUOUS inhabitant of a FIXED-SPACING `UniformCurvatureBound` via the geometric route — a finite
reversible CHARACTER-CHAIN surrogate of the SU(N) lattice YM Langevin generator that provably satisfies
`CD(K_S) > 0` at strong coupling (the Shen–Zhu–Zhu mechanism: free group-Ricci dominates the small Wilson
interaction Hessian), feeding `BakryEmery.eigenvalue_ge_of_CD` ⇒ a located gap ⇒ positive (fixed-spacing,
volume-uniform) mass via `UniformCurvatureBound`.

Honest framing (carried in every file): this is a DISCRETE character-surrogate REALIZING the SZZ mechanism,
not a verbatim port of SZZ's continuous-diffusion theorem; and it is a geometric SECOND PROOF of the
fixed-spacing gap (the cluster route already gives it). It does NOT reach the continuum — the functional-form
obstruction stands (a Bakry–Émery K analytic in g² cannot track exp(−c/g²); see
`uniform-cd-inhabitation-scope-2026-06-22.md`).

## What is reused (already proved, axiom-clean)

- `BakryEmery.lean`: `RevGen` (finite reversible Markov generator), `Gamma`/`Gamma2`, Dirichlet + Bochner
  identities, `CD`, `eigenvalue_ge_of_CD` (CD(K) ⇒ eigenvalue ≥ K), `locatedGapOfMargin` (the LocatedSpectralGap
  bridge). The discrete Bakry–Émery engine — consumed as-is.
- `HeatKernelCurvature.lean`: `freeDiag`, `casimirEig`, `free_DiagCD` (the FREE diagonal part has CD(3/4) =
  lowest Casimir), tensorization. The free anchor — the diagonal half of K_S.
- `UniformCurvatureBound.lean`: the structure to inhabit (`uniform_CD`, `toUniformClusterBound`,
  `curvatureBound_continuum_mass_isPositive`).
- `WilsonFunctional.lean`: `casimirQ`, `gramEntry`/`fusionLow` (the SU(2) Clebsch–Gordan fusion = the
  off-diagonal interaction coupling), the character moments.

## The mechanism (what each wave formalizes)

SZZ's Bakry–Émery constant `K_S = (N+2)/2 − 1 − 8N|β|(d−1)` = [group Ricci] − [Wilson Hessian]. In the
CHARACTER basis: the free Langevin generator is DIAGONAL (Casimir eigenvalues; gap = lowest Casimir = 3/4 for
SU(2), our `free_DiagCD`); the Wilson interaction is an OFF-DIAGONAL fusion (Clebsch–Gordan) coupling of
strength O(β). CD for the interacting chain = free curvature (3/4) − interaction-Hessian norm (O(β)); positive
for β below a threshold. This is the discrete shadow of SZZ.

## Wave decomposition

### Wave 1 — the character-chain generator + free anchor at chain level (ASSEMBLY; low risk)
- Define the finite reversible character-chain generator `charGen n` over states s<n: reversible w.r.t. the
  heat-kernel measure π(s) (= dim(s)²·e^{−tC₂(s)} or the normalized variant), free part diagonal with Casimir
  eigenvalues. Instantiate `BakryEmery.RevGen`.
- Reuse `free_DiagCD` / `HeatKernelCurvature` to prove the FREE chain has `CD(3/4)` at the `RevGen` level
  (bridge the diagonal-CD to the RevGen Γ₂ framework).
- Deliverable: `charGen` as a genuine `RevGen`; `charGen_free_CD : CD (charGen n) (3/4)`. Mostly assembly +
  reuse; the only real work is matching the diagonal-CD to the RevGen Γ/Γ₂ definitions.

### Wave 2 — the interaction perturbation + the Γ₂-smallness bound (THE CRUX; high risk)
- Add the off-diagonal fusion-coupling term `wilsonPert β` (the Wilson interaction surrogate: characters
  coupled by Clebsch–Gordan, strength scaling with β), giving the interacting generator `charGenInt n β`.
- PROVE the smallness bound: the perturbation's Γ₂-contribution is bounded by `C·β` (the SZZ O(|β|N)
  structure) — i.e. `Gamma2 (charGenInt n β) f ≥ Gamma2 (charGen n) f − C·β·Gamma f`. This is the genuine new
  estimate (the discrete Wilson-Hessian bound).
- RISK (flag honestly): (a) truncation edge effects at s=n can introduce spurious negative curvature — the
  bound must be uniform in the truncation or use a structure that avoids the edge; (b) the discrete Γ₂ of an
  off-diagonal perturbation is messier than the continuous Hessian — the O(β) bound may need a careful
  matrix-element estimate. If the clean O(β) bound does not close, the FALLBACK is to carry the interaction
  bound as a NAMED obligation `WilsonHessianSmall β C` (still leaving Wave 1's free anchor genuine) — honest
  partial progress, not a fake.

### Wave 3 — CD(K_S) at strong coupling + the fixed-spacing inhabitant + ledger (ASSEMBLY; low risk given Wave 2)
- Combine: `charGen_free_CD (3/4)` − Wave-2 bound `C·β` ⇒ `CD (charGenInt n β) K_S` with `K_S = 3/4 − C·β > 0`
  for `β < 3/(4C)` (the strong-coupling threshold). PROVE.
- Feed `eigenvalue_ge_of_CD` ⇒ located gap with margin from K_S.
- Inhabit a FIXED-SPACING `UniformCurvatureBound` (family indexed by volume, constant strong β, the single
  K_S) ⇒ `curvatureBound_continuum_mass_isPositive` ⇒ the geometric positive (fixed-spacing) gap. Non-vacuous.
- Consolidation ledger: state plainly it is a discrete surrogate of the SZZ mechanism, a geometric second
  proof of the fixed-spacing gap, NOT SZZ verbatim, NOT the continuum.

## Cost / odds / fallback

- Waves 1, 3: low risk (assembly + reuse of proved engine/anchor).
- Wave 2: the genuine difficulty and the gating risk (~50–60% the clean O(β) Γ₂ bound closes without a named
  residual, given the truncation/discrete-Hessian subtleties). Fallback on partial: free anchor (Wave 1) +
  named `WilsonHessianSmall` ⇒ a CONDITIONAL fixed-spacing inhabitant (still honest, still non-vacuous modulo
  one named smallness input — which is exactly the SZZ estimate).
- Overall: a multi-wave project (3 waves), realistic outcome = a fixed-spacing geometric inhabitant that is
  either unconditional (if Wave 2 closes) or conditional on one named SZZ-smallness estimate (if it doesn't).
  Either way it makes `UniformCurvatureBound` non-vacuous and records the geometric route as a genuine
  (second) proof path for the fixed-spacing gap.

## Honest caveats (non-negotiable, in every file)

- DISCRETE SURROGATE, not SZZ's continuous-diffusion theorem verbatim (our substrate has no manifold
  Γ-calculus; the character chain is the faithful discrete shadow).
- SECOND PROOF of the fixed-spacing gap (the cluster route already gives it) — does NOT advance the frontier.
- NOT the continuum: the functional-form obstruction (analytic-in-g² K vs exp(−c/g²) gap) is unchanged; K_S
  goes negative on the weak-coupling side. This build is explicitly fixed-spacing / strong-coupling.

## Recommendation

Proceed wave-by-wave with a checkpoint after Wave 2 (the crux). If Wave 2's O(β) bound closes, finish to an
unconditional fixed-spacing geometric inhabitant; if not, bank the free anchor + the named smallness obligation
(conditional inhabitant) and stop. Launch Wave 1 (low-risk assembly) to set the `RevGen` character-chain and
the free anchor at chain level; reassess at the Wave-2 checkpoint.
