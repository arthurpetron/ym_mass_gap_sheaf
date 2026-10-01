# Original finite slab quartic moment

Date: 2026-10-01 UTC. The scalar coefficient estimates now give a checked
quartic bound under the actual finite-slab spatial and terminal weight.
The complete finite character expansion, including every cutoff-boundary
term, is used. The result is relative to the SAME odd partition function,
not centered variance. It does not close the physical scaling or Clay target.

## The original source estimate

Put h=1-w, choose an integer S>=1, and define

    B(w,S) = 296*h^2 + 32*(S+2)^4*h^4 + 80*S^3*w^(S^2).

For a selected active link i, let r=2-chi_1 of its relative quaternion.
The exact original insertion satisfies

    selectedInsertion(r^2 * heatPrefix(w,K)) <= B(w,S) * oddMass(w,K,width,depth).

The guards are 0<w<1, K>=S+3, headCutoff(w)<=K,
1<=2*w^(4*(S+2)), and w^(S^2)<=1/8. These are explicit hypotheses,
not an asserted physical scaling trajectory. The bound is uniform in
cutoff K, width, depth and the selected active link under those guards;
its nome and split dependence is displayed. No physical time appears.

The precise declaration is
`BF4ExactSlabFixedSpatialQuarticMoment.selected_quartic_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialQuarticMoment.lean:53`).
It constructs the original endpoint source from the spatial factor and
terminal message, retains every unselected heat factor, constructs their
full pointwise positivity certificate, and uses the existing exact mass pin.
It does not replace the source by a centered probe, a factorized marginal
or a Perron eigenfunction. No inverse pointwise heat minimum is used.

## Signed finite regrouping

`SU2HeatQuarticFiniteRegroup.finite_regroup`
(`lean/YMGap/Continuum/SU2HeatQuarticFiniteRegroup.lean:335`) transposes
the original finite character sum against an arbitrary response Gamma.
The signed five-band matrix is symmetric, with diagonal five at spin zero
and six at positive spins, entries minus four at distance one, and entries
one at distance two. Finite Fubini on a common padded square proves the
identity. Exact support lemmas then remove only identically zero terms.

Input coefficients are the original a_j=(j+1)*w^(j*(j+2)) for j<=K,
zero otherwise. Output coefficients are retained through spin K+2.
No untruncated bulk coefficient is used at the upper boundary. The identity
holds also for K=0 and K=1, without positivity hypotheses.

`SU2QuaternionHeatQuarticMoment.quartic_value_regrouped`
(`lean/YMGap/Continuum/SU2QuaternionHeatQuarticMoment.lean:119`) applies
that equality to the actual Haar insertion with its unchanged spectator
kernel and same endpoint source. `prefix_value` in the same module pins
the comparison heat mass to those same responses and coefficients.

## Head and high tail estimates

The exceptional coefficients have exact polynomial factorizations by h^2.
Their checked bounds are b0<=60*h^2 and b1<=148*h^2 for 0<=w<=1:
`SU2HeatQuarticLowCoefficients.zeroCoeff_le_sixty`
(`lean/YMGap/Continuum/SU2HeatQuarticLowCoefficients.lean:216`) and
`oneCoeff_le_148` (same file, line 232). The spin-one bound is an upper
bound, not an absolute value or a presumed sign. `oneCoeff_le_relative`
(line 278) places it in the existing relative budget under its half-guard.

`SU2HeatQuarticHeadComparison.coefficient_head_bound`
(`lean/YMGap/Continuum/SU2HeatQuarticHeadComparison.lean:84`) combines
both exceptional spins with the bulk under one budget
296*h^2+32*L^4*h^4 for all j<L, L>=3, K>=L+1 and 1<=2*w^(4*L).
`head_response_bound` (same file, line 131) uses nonnegative responses
to pay that head by the complete SAME heat mass.

For j=k+2 in the tail, dropping negative neighbours gives
b_j^K<=a_k^K+6*a_(k+2)^K+a_(k+4)^K. Only here is the dimension upper
bound Gamma_j<=(j+1)*J used. Shifted dimension factors cost at most 3,6,1,
so the three positive tails cost at most ten times one padded
dimension-squared tail. The existing block bound then gives
80*S^3*w^(S^2)*J for every finite high-output interval starting at S+2.
The precise theorem is `SU2HeatQuarticTailComparison.high_response_tail_bound`
(`lean/YMGap/Continuum/SU2HeatQuarticTailComparison.lean:344`).

`SU2QuaternionHeatQuarticBound.prefix_quartic_bound`
(`lean/YMGap/Continuum/SU2QuaternionHeatQuarticBound.lean:102`) supplies
nonnegative character responses from the PSD spectator kernel and their
dimension cap from the full positive background certificate. The vacuum
channel gives J<=the original complete heat mass. The original slab
declaration above supplies all these hypotheses for its actual source.

## Remaining mathematical consumer

The radial Wilson increment contains a quartic correction for the WHOLE
word, whereas the new estimate controls one relative link. The next join
must retain the original word, edge weight and partition while lifting
this link control to the whole-word correction. The mixed radial moment
still requires a comparison with SAME interacting centered variance.
The consumer remains
`BF4ExactSlabFixedSpatialWilsonRadialIncrement.wilson_energy_radial_normalized`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonRadialIncrement.lean:154`).

A useful nome/split schedule and its physical time/scaling justification
are still missing. The formula B(w,S) is not itself a proved asymptotic
rate along a Yang--Mills trajectory. No full-word variance comparison,
continuum survival, physical mass calibration, QFT or all-group theorem
is supplied by this increment. Canonical chart states remain unchanged.

## Constructivity and verification

Seven final serialized focused checks passed, with 51 printed axiom gates
within {propext, Quot.sound}, including one diagnostic gate for an existing
finite-sum lemma. Two unused-variable warnings in the moment module are
harmless. No sorry, new axiom, native_decide, noncomputable declaration or
canonical-field weakening was added. Only the main agent compiled.

Intermediate checks caught forbidden classical dependencies from a broad
simplification and from applying omega directly to a conjunction. Explicit
conditional rewrites and constructing the conjunction before arithmetic
removed them. The final consumer gates are clean; intermediate elaboration
success was not accepted as constructive verification.

The monitored checks used one worker, a 20 GiB ceiling and 12 GiB OS reserve.
Process preflight found no competing compiler/test/runner; the memory query
reported 89% free. Every check completed in its initial call. No full root
build, full-tree audit or guard was run. Root imports were added, not compiled
as an aggregate. No ASCII chart was reprinted.

Final log SHA-256 values, all files under `/tmp/`:

- `ym-quartic-finite-regroup-20261001.log`:
  `76f1348abdb9d4f0b951b9a4cc4e5133b4406f26564b6c3c3c94d88ff396e1e4`.
- `ym-quartic-low-coefficients-20261001.log`:
  `63c5dfc2394a7afcf1b90e6c625a88749ff775a3181cafca4cd5c4d5ae38c769`.
- `ym-quartic-head-comparison-20261001.log`:
  `fac9cbfe5a39010a1291850985052b95fee4bd71f0b5c29cd6dad226aac091fd`.
- `ym-quartic-tail-comparison-20261001.log`:
  `e2666060cf760d847bb8087c02f5f88a4fcaececb7828033d3e72bcf8d1e9ff7`.
- `ym-quartic-moment-20261001.log`:
  `d38b26532a5d972463456a4c7ceabfddda77fa9394bbc893efca5b673e6acf62`.
- `ym-quartic-original-bound-20261001.log`:
  `ebc686388c602735fda547f437c6ad5130a458fff85bd0b3f8a91b366b266845`.
- `ym-quartic-physical-bound-20261001.log`:
  `505c8df5eb2c4b8fe6bdc33b117658a02380995cb45488375e7dac5c4c5f3070`.
