# Guarded coupling escape without an initial norm restriction

## Checked mathematical increment

On every valid ORIGINAL Wilson spatial-union completion, for a centered
state x define R_w(j)=B_w(x,T_w(j)x). Fix a positive ceiling W with its
explicit heat and entropy guards, and fix kappa>0. The computed onset

    N(W,kappa)=geometricCutoff(twoStepRate(W),1,kappa/2)

is independent of the smaller nome w, state, support and normalization.
If w<=W, n>=N(W,kappa), and kappa*R_w(2n)<=R_w(4n), then T_w(n)x=0.
Consequently a NONZERO smoothed image with this ratio forces w>W.
This also applies pointwise when the valid carrier, nome and vector vary
at every scale. No cross-carrier map or initial squared-norm cap is used.

All paths below are repository-relative and refer to the checked current source.

| Declaration | Source | Exact role |
| --- | --- | --- |
| `response` | `lean/YMGap/Continuum/BF4WilsonSpatialUnionMacroscopicRatioObstruction.lean:109` | Actual original B(x,T(j)x), not a reference certificate. |
| `relative_even_response_bound` | `lean/YMGap/Continuum/BF4WilsonSpatialUnionMacroscopicRatioObstruction.lean:113` | R_w(2*(start+n))<=theta(w)^n*R_w(2*start); uses the actual smoothed norm. |
| `twoStepRate_mono` | `lean/YMGap/Continuum/BF4ExactSlabCouplingRateMonotonicity.lean:85` | 0<=w<=W and the explicit heat guards imply theta(w)<=theta(W). |
| `ceilingRatioCutoff` | `lean/YMGap/Continuum/BF4WilsonSpatialUnionMacroscopicRatioObstruction.lean:165` | Returns N(W,kappa) as Nat data. |
| `relative_even_response_ceiling` | `lean/YMGap/Continuum/BF4WilsonSpatialUnionMacroscopicRatioObstruction.lean:171` | Replaces only the rate by theta(W); preserves each member's own response. |
| `macroscopic_ratio_image_zero_of_nome_le` | `lean/YMGap/Continuum/BF4WilsonSpatialUnionMacroscopicRatioObstruction.lean:191` | The common onset and the positive ratio force the original T_w(n)x=0. |
| `nome_gt_of_nonzero_macroscopic_ratio` | `lean/YMGap/Continuum/BF4WilsonSpatialUnionMacroscopicRatioObstruction.lean:218` | With T_w(n)x!=0, constructs the strict inequality W<w by rational order. |

The short proof is original norm decay on T_w(start)x, monotonicity of the
actual coupling-dependent rate, and cancellation of a positive RATIONAL
margin. The response itself is never inverted. Positive definiteness of
the SAME carrier then turns its zero squared norm into a zero vector.
No kinetic eigenpin, infinite-dimensional spectral theorem or erased
existence witness is involved.

## Nonvacuity and exact exclusions

The ceiling guards have an existing explicit positive instance: W=1/1024
is `nome` in
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCertificate.lean:32`, and
`existingNome_entropyRate` at
`lean/YMGap/Continuum/BF4ExactSlabSummableCoreRate.lean:37` proves its strict
entropy rate. Its heat guards are `existingNome_guards`,
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean:195`.
This is not a beta-independent claim or an uninhabited
arbitrary-rate interface.

The result excludes nonzero-image macroscopic-ratio families trapped below
ANY fixed guarded W, including arbitrary divergent scalar renormalizations.
It does NOT assert that x=0, that x!=0 implies T_w(n)x!=0, or that a single
positive response floor suffices. The bounded/polynomial SINGLE-response
results remain distinct:
`nome_gt_of_sampled_response`,
`lean/YMGap/Continuum/BF4WilsonGuardedCouplingEscape.lean:58`, and
`nome_gt_of_polynomial_response`,
`lean/YMGap/Continuum/BF4WilsonPolynomialScalingObstruction.lean:89`.
Their norm-budget hypotheses have not been deleted or weakened.

The theorem does not exclude approaching the open entropy boundary or
families leaving every fixed guarded ceiling. It does not identify that
boundary with a physical critical point, prove w tends to one, provide an
all-nome spatial completion, or furnish a continuum theory/mass gap.
The existing all-nome finite-width and guarded spatial-union carriers are
not silently identified. The whole Clay target remains OPEN.

## Concrete next analytic attempt, NOT a proved input

The actual backward consumer remains
`normalizedAnchorResponse_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`:
it takes the unsupplied SAME-source macroscopic ratio. Cross-scale control
also still takes its three relative costs in `dyadic_normalized_response_compare`,
`lean/YMGap/Continuum/BF4WilsonAllNomeThreeNormComparison.lean:313`.

Parallel source review isolates a more specific analytic attempt. For the
literal padded square with s=side(scale)>=2, t=s/2, original g=g_n, its
computed finite odd mean c_n, h=g*(f-c_n), A=T^t g, b=T^t h and ell=H[V*(-)],
retain the vacuum subtraction BEFORE estimates and seek a family-wide C in

    s*(ell(b*b)*ell(A*T A)-ell(b*T b)*ell(A*A))
         <= C*ell(b*b)*ell(A*T A).

This is an UNSUPPLIED estimate, not a new Lean theorem or frontier field.
The SAME finite c_n is retained on both sides; it is not reset to a mean
for either longer horizon. The partitions ell(A*A) and ell(A*T A) are
distinct. The finite-source/limit join and uniform changing-family budget
must still be proved. Available original folding ingredients are
`iterateStep_add`, `terminalPair_total` and `chain_partition_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMiddlePairing.lean:47`,
`:63` and `:102`, and `iterateStep_weighted_symmetric`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:128`.
The actual finite mean is `mean`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMeanRadial.lean:99`.

The existing `paddedSquare_own_commutatorGain_local_radial_bound`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainRadialCost.lean:258`,
is a squared MAGNITUDE bound with the original source-loss and trace-gap
costs. Neither cost has the needed relative comparison. A small magnitude
bound is not a favorable gain. The finite six-link bent-cube witness is a
different source from the actual planar growing square, whose perimeter is
4*side (`square_length`, `lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:65`).
No interchange of these observables is asserted.

## Verification boundary

Root ran one focused check of the changed module through
`scripts/safe_lean_build.py`, jobs=1, reserve=12 GiB, worker ceiling=20 GiB.
Fresh preflight showed 85 percent system-wide free memory, zero swap and no
competing Lean/Lake/pytest/runner. The check exited zero. Direct parsing of
the accepted log found eleven unique axiom records, all within
{propext, Quot.sound}; four are new, seven existing. There were no errors
or sorryAx. The original cosmetic unused-section-variable warning for
hw1 in `rate_at_ratioCutoff` remains unchanged. Independent read-only
mathematical review confirmed the nonzero-image premise and varying-carrier
scope. No full build, full axiom audit or baseline regeneration ran.

- Source SHA256: `384e20f151011c8ed2ab1abbd3f2321f81b0ee60a88691f1f161e4d781e5da0b`.
- Accepted log: `/tmp/ym-macro-ceiling-20261003-a.log`.
- Log SHA256: `8490761e519f5c26788b8d0385e3b93b0987db3ce10d9126793d13a779c55f1c`.

No new sorry/axiom, classical shortcut, resource-limit increase, canonical
field weakening or CI change. Exact displayed chart claims are unchanged;
the new restriction is supporting progress, not a continuum-node closure.
