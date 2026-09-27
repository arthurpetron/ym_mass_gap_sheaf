# Original Chebyshev cone, covariance pin, and the smaller analytic input

## Exact mathematical join

Let S be the existing eight-color conditional-projection sweep on the
original full-action completion, B=S* S, and X=cB-I for rational c.
Reversal of the adjoint schedule reverses both color order and order
within each color. The latter reversal does not change the operator,
because the actual same-color projections commute. Thus B is exactly
sixteen color layers, not a substitute operator.

For localized completed states x,y, the actual recurrence satisfies

    <T_n(cB-I)x,y> = T_n(c-1)<x,y>

whenever the 16*n Ward-star expansion of x's support misses y's support.
This uses the literal first component of the existing coupled recurrence.
It does not expand into absolute polynomial coefficients or discard signed
cancellations. Dividing by a positive rational T_n(c-1) preserves the
original pairing exactly. Centering the original polynomial observables
and retaining the original reciprocal partition identifies that pairing
with the existing normalized finite covariance. The rooted-carrier
coordinate separation condition is also proved sufficient.

These equalities are independent of any gap premise. They hold for every
0<w<1, K>=headCutoff(w), finite extent, rational c and natural n, with the
displayed localization/separation premises. The normalization additionally
requires positivity of its scalar denominator. No uniform decay in w or
lattice spacing is asserted.

## Source map

- `balanced_runLayers`,
  `lean/YMGap/Continuum/BF4ExactSlabBalancedCone.lean:89`: the actual B is
  the forward colors followed by reversed colors. The same module proves
  one-cycle and iterated localization and separated pairing.
- `coupled_first_localized`,
  `lean/YMGap/Continuum/BF4ExactSlabChebyshevCone.lean:124`: the degree-n
  first component has radius at most 16*n, not twice that radius.
- `coupled_cone_pairing`,
  `lean/YMGap/Continuum/BF4ExactSlabChebyshevPairing.lean:105`: the exact
  scalar Chebyshev pairing above. `normalizedFirst` (`:154`) constructs
  the normalized vector; `normalizedFirst_pairing` (`:162`) proves its pin.
- `covariance_as_chebyshev_pairing`,
  `lean/YMGap/Continuum/BF4ExactSlabChebyshevCovariance.lean:48`: original
  centering and reciprocal partition, without a comparison-factor loss.
  `covariance_as_chebyshev_pairing_of_root_far` (`:71`) consumes the literal
  root separation 16*n plus the two carrier sizes.
- `affine_norm_expansion`,
  `lean/YMGap/Continuum/BF4ExactSlabChebyshevRescale.lean:101`: the exact
  original squared-norm identity for arbitrary rational c.
  `coupled_first_norm_from_reverse_energy` (`:125`) and
  `normalizedFirst_norm_from_reverse_energy` (`:137`) consume the
  single-vector inequality below. They do not produce it.

## Smaller sufficient analytic input, still open

For a requested degree n and input x, put u=(coupled X x n).2. It suffices
to prove, on this actual auxiliary vector alone,

    c ||B u||^2 <= 2 ||S u||^2,       c >= 0.

The exact expansion is

    ||X u||^2 = ||u||^2 + c^2||B u||^2 - 2c||S u||^2.

The supplied inequality makes X contractive at u. The already checked
coupled quadratic invariant then bounds the first component by ||x||^2.
The SAME normalized vector occurring in the covariance pin has squared
norm at most T_n(c-1)^(-2)||x||^2. No global invariant-sector or all-state
gap hypothesis is needed by this consumer. To use the mechanism at a
family of degrees/observables, the actual inequality must be supplied for
each corresponding auxiliary vector. Useful rescaling (c>2), dependence
on volume, cutoff, coupling and spacing, and that producer remain open.
The known c=2 non-strict estimate does not supply accelerated decay.

No new structure or canonical frontier field was introduced. The explicit
`hrev` arguments of the two consumer theorems are the unsupplied input,
not a proved physical instance. A global original centered lower bound
remains a sufficient alternative; it is not declared necessary for Clay.

## Why the existing estimates do not fill that input

The following source audit is distinct from the new proofs above:

- `conditionalProjection_freeCentered_norm`,
  `lean/YMGap/Continuum/BF4ExactSlabStarLocalInfluence.lean:123`, requires
  deleted-form free-centering against every exterior probe. Original global
  mean zero is not this hypothesis.
- `free_sector_preservation_false`,
  `lean/YMGap/Continuum/SU2QuaternionHeatFreeSectorObstruction.lean:235`,
  refutes automatic preservation in the stated two-endpoint heat example.
  This does not refute the Yang--Mills target or the actual proposed bound.
- `dirichlet_comparison`,
  `lean/YMGap/Continuum/BF4ExactSlabPolynomialDirichletComparison.lean:189`,
  compares dense original residual energy with explicit polynomial energy;
  it contains no lower comparison with the globally centered variance.
- `eight_layer_energy_le_625_loss`,
  `lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:84`, is an
  upper bound on the final residual sum, not the missing lower bound.
- `terminal_normalized_energy_variance_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:284`,
  concerns the temporal marginal and its width-dependent mixFraction.
  It is not a volume-uniform estimate on this full-action carrier.

## Verification and remaining boundary

Five new modules passed focused serialized checks through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check ...`.
All 25 printed public gates report only `{propext, Quot.sound}`. Sol supplied
independent cone/rescaling proof work and a read-only mathematical review
of the pairing argument. No new sorry, axiom, classical input or weakened
canonical field. Root imports were added; no root/full-tree build, full
audit or guard was run. The focused checks finished in their initial calls;
there was no live job to poll repeatedly.

This is conditional-update geometry and an exact spatial-covariance pin,
not an identification of B with the physical-time OS transfer or Hamiltonian.
The actual reverse-energy/lower-estimate producer, useful spatial/scaling
rates, same-theory OS and continuum QFT, physical mass, nontrivial survival,
every compact simple group and the whole Clay target remain open. Canonical
chart markers are unchanged, so no chart reprint is warranted.
