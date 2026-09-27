# Original polynomial Dirichlet comparison

## Checked result and actual consumer

For every original supported polynomial p and physical link i, put
`fr_i(p)=p-J_i(freeAverage_i(p))`. Let F be the existing original full-action
form, D_i its star-deleted form, and C_i its actual completed conditional
projection. The new theorem proves

    L(w) D_i(fr_i(p),fr_i(p))
       <= ||(I-C_i) embed_F(p)||_F^2
       <= U(w) D_i(fr_i(p),fr_i(p)).

Here `L=lowerFactor`, `U=upperFactor`. The assumptions are the existing
`0<w<1`, finite extent, and `K>=headCutoff(w)`. No centering hypothesis is
imposed on p. Summing over any supplied list of physical links compares
the actual completed residual energy with the explicit rational
`polynomialEnergy`. Each D_i retains all complementary original face
factors; the different D_i are NOT one shared product-Haar background.

This gives a finite polynomial producer target for the missing centered
lower coercivity inequality without constructed conditional inverses.
Neither that lower inequality nor an all-degree finite-certificate scheme
is constructed here. The theorem concerns dense polynomial inputs; no new
extension theorem to arbitrary completed inputs is claimed.

## Declarations and proof

| Declaration | Source | Content |
|---|---|---|
| `polynomialEnergyAt` | `lean/YMGap/Continuum/BF4ExactSlabPolynomialDirichletComparison.lean:110` | Explicit rational star-deleted energy. |
| `polynomialEnergyAt_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabPolynomialDirichletComparison.lean:112` | Positivity of the same deleted form. |
| `residual_free_pin` | `lean/YMGap/Continuum/BF4ExactSlabPolynomialDirichletComparison.lean:118` | Exact original residual unchanged by subtracting the lifted free average. |
| `conditional_variance_comparison` | `lean/YMGap/Continuum/BF4ExactSlabPolynomialDirichletComparison.lean:158` | Two-sided all-polynomial comparison with L and U. |
| `polynomialEnergy` | `lean/YMGap/Continuum/BF4ExactSlabPolynomialDirichletComparison.lean:176` | Explicit sum with link-specific backgrounds. |
| `dirichlet_comparison` | `lean/YMGap/Continuum/BF4ExactSlabPolynomialDirichletComparison.lean:189` | Summed comparison on the single original completion. |

The actual conditional projection fixes every lifted exterior polynomial,
so subtracting the free average does not change its residual. For the lower
bound, the explicit free residual is orthogonal to exterior polynomials
in D_i. The deleted-form minimum inequality applies at EACH actual
conditional-Cauchy approximant, followed by the local original/deleted
form comparison. Passing this fixed floor to the constructed limit gives
exactly L times the deleted norm, not a weakened L-squared/U factor.
For the upper bound, residual projection is contractive on the full form,
then the upper original/deleted comparison costs U. Finally finite
ordered sums preserve both inequalities.

## Parameter and route limitations

`localFloor`, `lowerFactor`, and `upperFactor` are defined at
`lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:42`, `:44`, and
`:45`: `L=min(headFloor(w),1)^6`, `U=(1+prefixCap(w))^6`.
Their statements name w; these are NOT coupling-independent constants.
The existing `inverseRate_ge_sixtyThreeSixtyFour` at
`lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:56` already
precludes treating the associated coarse inverse rate as a small
neighbor influence. This comparison must not become an obligatory loss
on every scaling route. Sharper actual conditional estimates remain an
alternative to it.

The directly sufficient missing input remains a useful centered lower
bound for the SAME original Dirichlet energy. The previously checked
`eight_layer_energy_le_625_loss` at
`lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:84` is only
an upper bound in terms of actual sweep loss. Neither it nor this local
comparison proves the missing lower estimate. A direct centered lower
bound would avoid independently identifying the entire joint fixed space;
a lower bound restricted to the joint-fixed complement would still need
that sector join. Conditional sweeps are not physical time evolution.

## Targeted primary-source review

This review did not refresh the routine math-ph listing.

- [Caputo--Menz--Tetali, Approximate tensorization of entropy at high temperature](https://arxiv.org/pdf/1405.0608),
  Proposition 1.1 and Theorem 2.1: approximate entropy tensorization implies
  a Poincare bound; their sufficient criterion uses heat-bath ergodicity
  and conditional-density ratio influences with a strict row smallness
  condition. The stated main setting is discrete finite/countable spins.
  No such original SU(2) plaquette influence bound is supplied by this
  repository increment. This is a candidate analytic method, not a
  verified application or a physical Hamiltonian gap.
- [Caputo--Parisi, Block Factorization of Relative Entropy via Spatial Mixing](https://link.springer.com/article/10.1007/s00220-021-04237-1),
  Theorem 2.3 and sections 2.2.2, 2.2.4: strong spatial mixing gives
  volume- and boundary-uniform block entropy factorization. Compact
  continuous spins are discussed, but extension from the stated
  nearest-neighbor interactions to general finite-range interactions is
  explicitly non-immediate. The needed original-action mixing estimate
  and a justified plaquette adaptation are not proved here. The paper
  therefore does not remove the present scaling-regime obligation.

These sources suggest investigating retained-exterior conditional
influences or spatial mixing. They do not furnish the missing bound from
the local comparison alone. No external theorem was imported into Lean.

## Verification

The single new Lean module passed its focused monitored check in 2.30
seconds, one worker capped at 20 GiB. All six printed axiom dependencies
were exactly `{propext, Quot.sound}`, with no errors or warnings.
Sol independently reviewed both constants, residual invariance, distinct
deleted backgrounds and the original full-action pin. No new `sorry`,
axiom, analytic field, canonical frontier change or chart-marker change.
No full-tree build/audit was run. Useful global coercivity, physical
scaling, nontrivial continuum survival, full same-theory QFT structure
and every-group Clay closure remain open.
