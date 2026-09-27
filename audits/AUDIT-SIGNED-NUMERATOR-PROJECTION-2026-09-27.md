# Signed-numerator control of the actual conditional projection

## New estimate

Let F be the existing full original action, G_i the retained exterior
form, J_i its lift, M_i multiplication by the actual integrated star,
N_i the actual inserted numerator, and C_i the constructed completed
conditional projection. For every supported original polynomial p,

    L(w) ||C_i embed_F(p)||_F^2 <= G_i(N_i p,N_i p).

This holds for every physical link, finite extent, 0<w<1 and
K>=headCutoff(w). It does not require a supplied inverse or smallness
hypothesis. L is the existing positive six-face lower factor, not a
coupling-independent constant.

For f=p-J_i(A_i p), where A_i is the computed free-link average, the
same numerator energy equals the retained-exterior squared norm of

    N_i p - M_i(A_i p).

The signed difference is formed before squaring. This is equality of
form values, proved through the radical relation, not equality of raw
polynomial coefficients. The residual `(I-C_i)f` is the residual of p
itself by the earlier exact free-centering pin.

## Causal proof

The finite identity behind the estimate is

    L F(p-J_i r,p-J_i r) - L F(p,p) + G_i(N_i p,N_i p)
      = G_i(Lr-N_i p,Lr-N_i p)
        + L [G_i(r,M_i r)-L G_i(r,r)] >= 0.

The original probe pairings and proved local normalizer floor give both
nonnegative terms. Applying this to EVERY actual exterior inverse-Cauchy
approximant passes the inequality to the original completed residual.
The checked single-projection Pythagorean identity then bounds C_i p.
No division by a possibly null vector norm or quotient representative
selection occurs.

| Declaration | Source | Checked content |
|---|---|---|
| `numeratorEnergy` | `lean/YMGap/Continuum/BF4ExactSlabStarNumeratorInfluence.lean:97` | Explicit rational norm after actual signed Haar integration. |
| `numeratorEnergy_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabStarNumeratorInfluence.lean:99` | Positivity in the retained exterior form. |
| `probe_variational_bound` | `lean/YMGap/Continuum/BF4ExactSlabStarNumeratorInfluence.lean:103` | Finite square-completion bound for every exterior test. |
| `conditional_residual_bound` | `lean/YMGap/Continuum/BF4ExactSlabStarNumeratorInfluence.lean:124` | Bound on the actual completed residual. |
| `conditional_norm_bound` | `lean/YMGap/Continuum/BF4ExactSlabStarNumeratorInfluence.lean:161` | Numerator-sensitive original projection norm bound. |
| `centered_numerator_energy` | `lean/YMGap/Continuum/BF4ExactSlabStarNumeratorInfluence.lean:175` | Signed numerator-minus-normalized-average difference in the same form. |
| `free_residual_variance_bound` | `lean/YMGap/Continuum/BF4ExactSlabStarNumeratorInfluence.lean:203` | Retains original p's residual and free-residual numerator cancellation. |

## What this does not prove

The right-hand numerator energy is not shown small. The variance lower
expression obtained by subtracting it may even be negative. Unlike a
coarse L/U bound on the entire input, this estimate keeps the actual
signed correction available for further analysis; it is not universally
claimed sharper. L(w) still deteriorates, so a useful estimate relative
to L remains necessary. No neighboring conditional-influence coefficient,
global centered coercivity, spatially uniform contraction, physical-time
gap or scaling limit follows here.

Source review distinguishes two existing alternatives:

- `conditionalProjection_localRepresentative`, in
  `lean/YMGap/Continuum/BF4ExactSlabStarConditionalLocality.lean`, constructs
  bounded-support approximants, not a neighboring norm estimate.
- `two_link_dual_bound`, in
  `lean/YMGap/Continuum/SU2QuaternionWeightedProductTwoLinkDual.lean`, and
  `dualTest_cross_pin` / `actual_signed_two_link_bound`, in
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLinkDual.lean`, concern
  temporal marginals and retain signed cross terms. They do not establish
  a small coefficient for these original fullData conditional operators.

The next analytic task is to control actual signed numerator differences
or a sharper direct centered energy expression. A separate constructive
centered-density task can prepare its completed consumer without assuming
the missing analytic bound. The Clay target remains open.

## Verification

The new module passed a focused monitored one-worker check capped at
20 GiB; all seven printed dependencies were `{propext, Quot.sound}`.
The final check had no errors or warnings. An initial check exposed a
multiline pattern-lambda indentation error, corrected without changing
the bound. Sol independently reviewed the original-action pairings,
square identity, completion step and radical-level numerator identity.
No new source hole, axiom, analytic field or canonical edit. No full-tree
build/audit or routine literature listing refresh was run. Canonical
chart markers remain unchanged; no unchanged chart is reprinted.
