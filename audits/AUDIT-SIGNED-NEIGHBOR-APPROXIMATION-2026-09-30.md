# Original signed neighboring-pair sum: energy-relative approximation

Date: 2026-09-30 UTC. Parent source baseline: `2e0e3e8`.

## Checked result

Fix the original SU(2) full-action completion, rational nome `0<w<1`,
finite extent and heat cutoff `K>=headCutoff(w)`. For a supported polynomial
`p`, write `r_i=R_i p`, `E_i=||r_i||^2`, `E=sum_i E_i` and
`H=sum_i R_i`. The existing conditional-kernel polynomials give `t_i(n)`.
For `delta>0` and `n>=relativeCutoff(w,delta*delta)`, define the finite
rational value using the SAME original pairing:

```
V_n(p) = sum_{ordered distinct adjacent i,j} <t_i(n),t_j(n)>.
S(p)   = sum_{ordered distinct adjacent i,j} <r_i,r_j>.
c(delta) = 50*(delta + delta^2/2).

-c(delta)*E <= S(p)-V_n(p) <= c(delta)*E
E + V_n(p) - c(delta)*E <= ||H p||^2.
```

The code uses two order inequalities in the completed real quotient,
not an assumed absolute-value operation. The last inequality is
unconditional under the displayed scalar/cutoff guards; it does NOT
assert that its lower bound is positive.

## Declaration map

| Declaration | Source | Role |
| --- | --- | --- |
| `pairErrorCoefficient` | `lean/YMGap/Continuum/GNSPairApproximationError.lean:27` | Explicit rational `delta+delta^2/2`. |
| `pairing_young` | `lean/YMGap/Continuum/GNSPairApproximationError.lean:120` | Both signs of completed pairing controlled by endpoint energies. |
| `pair_error_bounds` | `lean/YMGap/Continuum/GNSPairApproximationError.lean:322` | Local two-sided Gram-entry error from the two relative residual errors. |
| `endpoint_charge_bound` | `lean/YMGap/Continuum/RCDirectedPairError.lean:184` | Separate directed row and column counts give `2*degree` endpoint charges. |
| `pairSum_error_bounds` | `lean/YMGap/Continuum/RCDirectedPairError.lean:252` | Sum the errors without discarding the signed values being approximated. |
| `offNeighbor` | `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:70` | Exactly ordered distinct adjacency from the original schedule. |
| `residualPolynomial` | `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:91` | Existing actual polynomial residual approximation. |
| `neighborValue` | `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:97` | Finite rational original-action signed Gram sum. |
| `neighborValue_pin` | `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:103` | Its exact embedding into the same completed inner product. |
| `neighborErrorCoefficient` | `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:133` | Explicit coefficient `50*pairErrorCoefficient(delta)`. |
| `signedNeighbor_error_bounds` | `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:137` | Original-action two-sided signed-sum error. |
| `conditionalGenerator_square_polynomial_lower` | `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:189` | Direct lower-bound consumer for the original conditional generator square. |

## Short argument and original-object joins

Put `e_i=r_i-t_i`. Bilinearity gives
`<r_i,r_j>-<t_i,t_j>=<e_i,r_j>+<r_i,e_j>-<e_i,e_j>`.
Weighted Young bounds the two mixed terms together by
`delta*(E_i+E_j)` and the error-error term by
`delta^2*(E_i+E_j)/2`. Division uses only the positive rational
`delta`, never a residual energy or a spectral margin.

The actual relative-error input is
`BF4ExactSlabStarEnergyRelativeApproximation.residual_energy_relative_error_le`,
`lean/YMGap/Continuum/BF4ExactSlabStarEnergyRelativeApproximation.lean:169`.
The returned approximation index is the existing computable
`relativeCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabStarResidualApproximation.lean:241`.

Each endpoint is charged at most 25 times in each direction, by
`neighborhood_row_count`,
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:98`, and
`column_count`,
`lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:35`.
Thus the coefficient is 50, with no link-count multiplier. The bound
25 includes the diagonal; using it for the distinct-pair mask is a safe
overestimate. No symmetry assumption on an arbitrary directed pair field
is used in the generic summation theorem.

The final join uses `signed_energy_le_generator_square`,
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:85`:
remote pairs contribute nonnegative composed-residual squares. The actual
operator is `conditionalGenerator`,
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:46`, on the
original full-action completion. It is conditional-link dynamics, NOT
the physical OS transfer or Hamiltonian.

## Quantifiers, cost and remaining input

The error coefficient is independent of nome, extent, late heat cutoff,
link placement and polynomial degree. Its iteration cutoff depends
explicitly on `w` and `delta`, but not on those other parameters. This
does not provide a nome-uniform iteration bound or efficient evaluation:
the existing unreduced-rational cutoff can be very large. No large
calculation was launched.

The actual-action theorems quantify over EVERY supported polynomial
input, of arbitrary degree, embedded in the completion. They do not
construct an approximation map for every completed vector. The generic
pairing lemma itself allows completed vectors, given its explicit error
bounds.

This closes the signed-neighbor approximation-error step left after the
local residual result. The useful lower bound on `V_n(p)` relative to
`E(p)` remains unproved. Checking a finite principal matrix would not
establish it for all polynomial degrees: omitted-mode and kernel control
still have to be supplied. An eventual auxiliary-orbit application needs
the estimate on every required orbit state, not just its initial input.
No new conditional margin wrapper or analytic hypothesis was introduced.

A03, justified physical scaling, continuum survival, same-theory OS/QFT
structure, physical mass and every-group closure remain open. No canonical
chart claim changed, so the chart was not reprinted.

## Verification

Three serialized focused checks used the monitored launcher, one worker
and the mandatory 20 GiB ceiling:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/<Module>.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
```

Final successful runs: `RCDirectedPairError` (about 0.3 seconds),
`GNSPairApproximationError` (about 2 seconds), and
`BF4ExactSlabSignedNeighborApproximation` (about 7.2 seconds).
All 16 printed declaration gates are subsets of `{propext, Quot.sound}`.
Two harmless unused-simp-argument warnings remain in `neighborValue_pin`.
No new sorry, axiom, classical step or native oracle. No full-root build,
whole-tree audit or numerical certificate search was run. Root imports
are registered; this is not a claim of full-root verification.

Sol implemented the generic pairing estimate; Luna implemented the
directed endpoint accounting, with parent integration and focused checks.
Luna also independently reviewed the original-action join, both incidence
counts, cutoff quantifiers and the absence of a positive-margin claim;
no substantive scope or mathematical issue was found.
