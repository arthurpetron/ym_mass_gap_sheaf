# Original full-product angular defect without inter-step commutation

Date: 2026-09-23. Parent revision: `500e9ab`.

Whole-project goal remains OPEN: constructive Lean nontrivial continuum
Yang--Mills on R^4 for every compact simple group, full same-theory QFT and
Yang--Mills local-field/short-distance structure, isolated vacuum and a finite
positive physical Hamiltonian mass gap.

## Actual quantitative endpoint

`productMap_range_defect_le_two_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularDefect.lean:161`, proves

```
H_n(p*p) - H_n(p * productMap n w K (List.range n) p)
  <= 2*(1-w) * sum_{i<n} H_n(blockAngularSquare i p).
```

Here n=tail+1, p is any supported signed rational quaternion polynomial,
`0 <= w < 1`, and `sufficientCutoff w <= K`. There is no centering,
pointwise heat-floor premise, assumed operator realization, or commutation
input. The coefficient `2*(1-w)` is independent of n and K; the sum still
contains n original-block energies. This is a defect upper bound, not a
strict spectral-gap lower bound.

The fully active ORIGINAL product is pinned by the existing
`productMap_range_cycle_carrier`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicFold.lean:144`.
The new `productMap_range_defect_le_rotated_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularDefect.lean:140`, consumes
this pin after the reference returns to the original p. The final theorem
then rewrites every rotating angular cost to its original block.

## Mathematical contraction of the proof path

For a symmetric positive contraction P, put D=I-P and
`Phi_x(y)=<y,y>-4<x,y>+3<x,x>`. Two nonnegative expressions suffice:

1. `D(2x-y,2x-y) >= 0`;
2. `<y,Py>-<Py,Py> >= 0`.

Adding them gives `Phi_x(Py)<=Phi_x(y)+4*D(x,x)`. Also
`Phi_x(y)=2*(<x,x>-<x,y>)+<x-y,x-y>`.
Telescoping from y=x therefore bounds the endpoint defect by twice the sum
of fixed-reference local defects. This avoids both inter-step commutation
and a joint spectral decomposition; no square root or spectral theorem is used.

The generic checked declarations are `potential_step`,
`lean/YMGap/Continuum/PositiveContractionProductDefect.lean:60`, and
`path_defect_bound`, same file line 119. They are actually consumed by
`cycleIterate_rotated_defect_le_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularDefect.lean:110`.
For cyclic step C=R headMap, both the evolving input and its reference rotate
by R. Haar isometry preserves the potential. The local costs are evaluated
on R^i p, not on a repeatedly smoothed substitute for p.

The remaining algebraic pins are:

- `rotateIterate_period_carrier`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicRotationPeriod.lean:122`:
  R^n p equals p under every Haar insertion on the supported n-block carrier.
- `rotateIterate_headAngularSquare_haar_of_lt`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicAngularEnergy.lean:84`:
  the head energy of R^i p is the original block-i energy for i<n.

Sol supplied the two rotation/transport drafts; root repaired elaboration,
checked the gates and proved the actual potential/product consumer. Luna
independently reviewed the algebra and final source scope.

## Consumer and remaining frontier

The sharper factor-one target remains OPEN and unchanged. This is a separate
proved factor-two theorem; no canonical field or existing statement is weakened.
Commutation/joint modes may sharpen the constant but are not prerequisites
for the theorem now proved.

The intended interacting consumer is `energy_eq_bare_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`.
Its proper active list is NOT `List.range n`: inactive Haar projections must
still be accounted for. Its complete input is `V*g*f`, and its correction is
signed. In particular the factor-two bare estimate does not itself cancel
endpoint-source derivatives against that correction. The earlier exact
head-angular cancellation identity is not silently applied with a changed
coefficient. These are the next original-action obligations.

No claim is made about physical OS/time identification, spatial/spacing
uniformity, continuum survival, full QFT, physical mass or other groups.

## Verification boundary

Accepted serialized checks, all terminal exit 0, one worker and 8 GiB cap:

- `/tmp/ym-gap-product-defect-potential-check-2.log`: five gates;
- `/tmp/ym-gap-cyclic-rotation-period-check-2.log`: five gates;
- `/tmp/ym-gap-cyclic-angular-energy-check-1.log`: three gates;
- `/tmp/ym-gap-product-heat-angular-defect-check-2.log`: three gates.

All sixteen printed gates contain only `{propext, Quot.sound}` (one uses
only `propext`). Accepted logs contain no warning, error, `sorryAx` or
`Classical.choice`. Earlier elaboration-error drafts are not evidence.
No new `sorry`, axiom, classical exception or changed frontier field.
Root imports are registered; no full-root build/audit/guard was run.
CI remains unchanged.

## Original-slab projected-source follow-up (2026-09-24 UTC)

The proper-active-subset obstacle above is now reduced for fringe-independent
observables, without requiring the complete endpoint source to be independent.
For `q=P_F(a)`, exact signed bilinear projection gives

    H[(a*p)*P_active(a)] = H[(q*p)*P_full(q)],
    E_active(a,f) = E_full(q,f).

The first identity requires p to omit F; the second requires f to omit F.
Support, disjointness and range-coverage guards are explicit. These identities
have no positivity/cutoff premise. The angular consequence retains the
existing `0 <= w < 1` and `sufficientCutoff w <= K` guards:

    E_full(q,f) <= 2*(1-w)*sum_i H[Gamma_i(q*f)]
                  + H[q*f^2*(P_full(q)-q)].

There is no separate inactive residual. The correction is signed and is NOT
discarded, declared nonpositive or set to zero by a stationarity premise.
The prefactor is independent of width/cutoff, but the source, angular sum
and correction are not bounded uniformly by this statement.

### Declarations and actual consumer

- `productMap_inactive_to_full_bilinear`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatInactiveBilinear.lean:37`:
  signed projection of both entries and restoration of missing factors.
- `sourceMoment_project`, `sourceEnergy_project`,
  `sourceEnergy_le_projectedAngular_add_correction`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatProjectedSourceEnergy.lean:70`,
  `:85`, `:139`: exact inserted moments/full energy, then angular upper bound.
- `energy_source_pin`, `energy_projected_source`, `oddMoment_projected_source`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:81`,
  `:102`, `:117`: ORIGINAL transfer, source `V*g`, and actual odd marginal
  `(V*g_n)*g_(n+1)`. The insertion theorem covers 1, f and f*f under their
  support/independence guards, so normalization and centering need not change.
- `characterFace_independent_index`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceIndependence.lean:139`, and
  `plaquette_fringe_independent_after_padding`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFringeIndependent.lean:48`:
  derive the literal character's fringe independence from strict padding.
- `padded_plaquette_energy_le_projectedSourceAngular_add_correction`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:196`:
  actual padded-plaquette/terminal-message consumer, with no manual activity
  or source-independence premise.

Sol independently reviewed the energy and moment pins and the signed
correction. This is not a duplicate of `ActiveEnergy.energy_active`: that
theorem peels the spatial weight under Haar and retains the partial transfer;
this result projects the COMPLETE source and uses the full product kernel.

### Remaining mathematical task and verification

Useful SAME-variance control of the full projected-source expression remains
open. An observable family must still be constructed and tracked through a
justified scaling trajectory. The separate EVERY-vector spatial/spacing gap,
same-theory continuum/QFT/YM fields, physical mass and every group remain open.
No canonical frontier field was changed and no new hole/axiom was introduced.

Accepted serialized checks, each terminal exit 0, one worker and 4 GiB cap:

- `/tmp/ym-gap-inactive-bilinear-check-1.log`: one gate;
- `/tmp/ym-gap-projected-source-energy-check-1.log`: four gates;
- `/tmp/ym-gap-face-character-independence-check-1.log`: seven gates;
- `/tmp/ym-gap-plaquette-fringe-independent-check-1.log`: two gates;
- `/tmp/ym-gap-original-projected-source-energy-check-1.log`: six gates.

All twenty printed gates use only {propext, Quot.sound}; accepted logs contain
no error/warning/sorryAx. Semantic consumer import added. No full-root
build/audit/guard was run; GitHub CI remains unchanged (disabled).

## Computed full-product Taylor follow-up (2026-09-24 UTC)

### Mathematical statement and same-object consumer

The actual fresh-output cyclic heat sweep is expanded into a finite computed
tree. Every edge carries its head harmonic degree; a leaf carries the product
of the ACTUAL truncated attenuations along its path. With path Casimir
`c=sum_d d*(d+2)` and eps=1-w, the scalar remainder r satisfies

    0 <= r = productAttenuation-1+eps*c <= eps^2*c^2

under `0 <= w < 1` and the explicit `sufficientCutoff w <= K` guard. This
includes degrees omitted by K: no degree-at-most-cutoff premise is imposed.

Unweighted reassembly recovers the original polynomial on the Haar carrier.
For a fixed supported p and an arbitrary signed test, the resulting identity is

    H[test*P_full(p)] = H[test*p] - eps*C(p,test) + R(p,test),
    -eps^2*B(p,test) <= R(p,test) <= eps^2*B(p,test).

C is the computed signed leaf pairing weighted by total Casimir, and B is
the sum of absolute leaf pairings weighted by its square. The scalar r is
nonnegative; the PAIRING remainder R is not asserted to be nonnegative.
No joint orthogonality or joint spectral diagonal positivity is used.

Apply the identity to BOTH terms of the existing full weighted energy:

    E(a,f) = H[a*f^2*P_full(a)] - H[(a*f)*P_full(a*f)]
           = eps*(C(a*f,a*f)-C(a,a*f^2))
             + R(a,a*f^2)-R(a*f,a*f)
          <= eps*sourceFirstOrder(a,f) + eps^2*sourceTaylorBudget(a,f).

The two zeroth-order terms cancel before estimates. Both absolute remainder
budgets are retained. The original signed source correction is already in E,
not an additional term to be counted again.

`BF4ExactSlabFixedSpatialSourceTaylor` takes `a=q=P_F(V*g)` after the earlier
exact inactive-source reduction. Its padded literal-plaquette theorem uses
the original terminal message, spatial action and temporal energy. Existing
`oddMoment_projected_source` still preserves mass, mean and second moment;
the new estimate does not normalize against a different law.

### Declaration evidence

- `productRemainder_bounds_of_sufficientCutoff`,
  `lean/YMGap/Continuum/SU2HeatProductTaylorRemainder.lean:229`.
- `productMap_modeFold`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicHeatModeExpansion.lean:194`,
  uses the carrier-preserving cyclic linearity in `SU2QuaternionCyclicHeatLinear`.
- `full_modeFold_one_carrier`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicModeReassembly.lean:137`.
- `productPair_taylor`, `pairRemainder_le_quadratic`,
  `neg_pairRemainder_le_quadratic`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicModeTaylor.lean:271`, `:314`, `:321`.
- `sourceFirstOrder`, `sourceTaylorBudget`, `sourceEnergy_taylor`,
  `sourceEnergy_le_firstOrder_add_quadratic`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatSourceTaylor.lean:35`, `:41`,
  `:47`, `:82`.
- `energy_taylor`, `padded_plaquette_energy_le_firstOrder_add_quadratic`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceTaylor.lean:61`, `:100`.

### What remains and verification boundary

At that checkpoint the first-order coefficient was computed, not yet identified with
`sum_i H[a^2*Gamma_i(f)]`. The next concrete identity is
`C(p,test)=-sum_i H[test*Delta_i(p)]`, requiring actual block-indexed
Laplacian transport through the cyclic rotations. Existing head Casimir and
weighted angular cancellation results do not themselves supply that join.
Even after that identification, useful control of the resulting first-order
term and remainder against SAME centered variance is still needed.

For fixed p,test, the tree and B have no nome/cutoff arguments. For the
original source q, however, their polynomial input depends on w,K,width and
terminal depth. The squared total-Casimir budget may grow with source degree
and carrier size; no uniform bound or useful changing-scale asymptotic is
proved. ONE-family survival, EVERY-vector spatial/spacing gap, SAME-theory
continuum/QFT/local YM fields, physical mass and every group remain open.
No canonical field changed and no new hole/axiom was introduced.

Sol produced scalar/linearity/reassembly and Taylor drafts; Luna independently
reviewed the signed energy formula and the two-budget scope. Accepted checks
were serialized, one worker, 4 GiB cap, each terminal exit 0:

- `/tmp/ym-gap-product-taylor-scalar-check-3.log`: five gates;
- `/tmp/ym-gap-cyclic-heat-linear-check-4.log`: fifteen gates;
- `/tmp/ym-gap-cyclic-mode-expansion-check-3.log`: six gates;
- `/tmp/ym-gap-cyclic-mode-reassembly-check-2.log`: three gates;
- `/tmp/ym-gap-cyclic-mode-taylor-check-4.log`: four gates;
- `/tmp/ym-gap-product-source-taylor-check-1.log`: two gates;
- `/tmp/ym-gap-original-source-taylor-check-2.log`: three gates.

All thirty-eight printed gates lie within {propext, Quot.sound}; accepted
logs contain no error/warning/sorryAx. Earlier failed drafts are not evidence.
Semantic consumer import added; no full-root build/audit/guard was run.
CI remains unchanged (disabled).

## Full-product source-cancellation follow-up (2026-09-24 UTC)

The first-order identity left open above is now proved for the full product:

    C(a*f,a*f)-C(a,a*f^2) = sum_i H[a^2*Gamma_i(f)].

This is an actual identity on the original Haar carrier, for arbitrary signed
supported polynomial a,f, not a source-stationarity assumption. The proof
first identifies the computed Casimir tree with a differential cyclic sweep.
Pairing a sweep in its own rotating frame emits the head negative-Laplacian
pairing plus the next rotated problem. Head integration by parts and the
existing weighted cancellation eliminate all derivatives of a at first
order. Weighted coordinate transport, not merely unweighted Haar invariance,
identifies the emitted head energies with all original block energies.

Consequently the existing original-source consumer now proves

    E_original = eps*sum_i H[q^2*Gamma_i(f)]
                 + R(q,q*f^2)-R(q*f,q*f),
    E_original <= eps*sum_i H[q^2*Gamma_i(f)] + eps^2*B(q,f),
    q = P_F(V*g),  eps = 1-w.

The upper bound uses 0<=w<1 and the existing computed sufficient-cutoff
guard. It does not require the source degrees to lie below the cutoff.
The exact identity requires no positivity of a or f. B is the sum of BOTH
absolute leaf-pairing remainder budgets. The source correction is already
inside the full energy and is not added again. Strict spatial padding
constructs fringe independence for the literal plaquette; no fringe
independence is imposed on the endpoint source.

### Declaration evidence

- `branchCasimir_head_carrier`, `branchCasimir_rotation_carrier`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicHeadCasimir.lean:179`, `:213`.
- `modeFold_casimir_carrier`, `pairCasimir_sweep`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicCasimirSweep.lean:216`, `:247`.
- `rotateIterate_head_weightedAngularSquare_haar_of_lt`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicWeightedAngular.lean:178`.
  This uses the existing, now public and axiom-gated
  `SU2QuaternionAngularReindex.reindex_blockAngularDerivative_prefix`;
  that theorem's statement and proof are unchanged.
- `sourceSweep_succ`,
  `lean/YMGap/Continuum/SU2QuaternionCyclicSourceCancellation.lean:148`.
- `sourceFirstOrder_eq_weightedAngularEnergy`, `sourceEnergy_taylor_angular`,
  `sourceEnergy_le_angular_add_quadratic`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularTaylor.lean:91`, `:107`, `:121`.
- `energy_taylor_angular`, `energy_le_angular_add_quadratic`,
  `padded_plaquette_energy_le_angular_add_quadratic`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceTaylor.lean:129`, `:148`, `:169`.

### Remaining analytic input and verification

The first-order derivative cancellation is closed; useful SAME-variance
control is not. q depends on w,K,width and terminal depth. Its square is
NOT identified with the original odd marginal `(V*g_n)*g_(n+1)`. Neither
the angular cost nor B has been bounded usefully along a justified
changing-scale observable family. In particular, eps^2 alone is no scaling
estimate when the polynomial source and its degrees change.

The existing fixed-width consumer is
`BF4ExactSlabFixedSpatialJointTemporalEnergy.centered_relative_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:128`:
a supplied one-step energy/variance bound propagates linearly in time on
the SAME centered completed state. The present finite Taylor identity does
not supply a scaling-useful bound to that consumer. The guarded spatial
union is not identified with this all-nome fixed-width carrier.
ONE-family survival, EVERY-vector spatial/spacing gap, full SAME-theory
QFT/local YM/UV identification, physical mass and every group remain open.

Sol repaired the recurrence and wrote the original-slab consumers; Luna
independently reviewed signs, the unchanged source and both retained budgets.
Seven accepted leaf checks were serialized with one worker and 4 GiB cap,
each terminal exit 0:

- `/tmp/ym-gap-angular-reindex-export-check-1.log`: four gates;
- `/tmp/ym-gap-cyclic-head-casimir-check-1.log`: seven gates;
- `/tmp/ym-gap-cyclic-casimir-sweep-check-2.log`: five gates;
- `/tmp/ym-gap-cyclic-weighted-angular-check-4.log`: five gates;
- `/tmp/ym-gap-cyclic-source-cancellation-check-2.log`: four gates;
- `/tmp/ym-gap-product-angular-taylor-check-2.log`: three gates;
- `/tmp/ym-gap-original-source-angular-taylor-check-1.log`: six gates.

All thirty-four printed gates lie within {propext, Quot.sound}; accepted
logs contain no error/warning/sorryAx. Failed drafts are not verification
evidence. The existing original-source import in `lean/YMGap.lean` covers
the new dependencies. No full-root build/audit/guard, new hole/axiom or
canonical-field change. CI remains unchanged (disabled).
