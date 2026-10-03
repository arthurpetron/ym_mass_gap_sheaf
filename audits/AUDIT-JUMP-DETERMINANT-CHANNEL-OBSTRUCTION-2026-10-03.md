# Signed determinant channels: a failed nome-interpolation shortcut

The unchanged goal is nontrivial continuum Yang--Mills on R^4 for every
compact simple group, with SAME-theory QFT axioms and a positive physical
Hamiltonian mass gap. It remains OPEN. This diagnostic concerns a proposed
comparison for the mixed-current determinant cost, not a Yang--Mills
counterexample or a favorable relative estimate on a changing family.

## The exact missing positivity premise

The existing `productChannels_nome_interpolation` requires a functional F
to be nonnegative on EVERY supported quaternion polynomial. Its statement
is conditional, and is not contradicted here. A heat-channel weight being
nonnegative does not give that property to its tested functional.

With one link, bare Haar law, V=g=1 and source b, the new functional is

    F_b(p) = H[p*b^2]*H[p] - H[p*b]^2.

For any Haar-centered b, the exact ratio-free identity is
F_b(b) = -H[b^2]^2. More concretely, take b=2*x0 and the ACTUAL fundamental
representation-column leaf p=x0. Its value is -1/4. The source proves that
this leaf belongs to the original heat-channel list and to the original
Casimir-tagged spectral list, and that it has supported coordinates.
Thus the nonnegative-functional premise fails on a literal channel, not a
manufactured coefficient array.

## Strict failure on the actual product-channel list

Take the second character b=4*x0^2-1, whose original Haar mean is zero
and Haar square is one. Define D(w) with the EXISTING unnormalized
`channelSum (productChannels 1 w 2 [0]) F_b`, retaining every channel
through cutoff two. The source computes the exact three values

    D(0) = 1,    D(1/2) = 255/256,    D(1) = 0.

At nome 1/2, the proposed interpolation without its positivity premise
has right side (1-w^3)*D(0)+w^3*D(1)=7/8. The source proves the STRICT
reverse inequality 7/8 < 255/256. All its other guards are satisfied:
one block, selected index zero, cutoff two and nome in [0,1]. Deleting
the positivity premise would therefore give a false theorem.

The endpoint nomes are finite algebraic evaluations; no endpoint kernel
positivity, continuum interpretation or BF4 cutoff guard is assumed.
This diagnostic does not substitute b for the particular original
BF4 filtered message T(g_n*(f-c)). It does not show that every
action-dependent signed comparison fails. It specifically excludes a
universal application of the existing positive-functional interpolation
to this determinant functional without establishing its premise.

## Consequence for the forward-backward plan

The original mixed-current source still reaches C1-C2 on the SAME
completed carrier. Its relative signed estimate is still unpaid. Keep
the determinant's signed channel contributions; positive channel weights
alone cannot justify discarding or interpolating their tested signs.
The alternative SAME macroscopic-response ratio remains unpaid as well.

The main backward input stays the COMBINED original energy and signed
multiplication cost against half-smoothed ell(b^2), retaining the OWN
center and BOTH original partitions, on a JUSTIFIED changing family.
No fixed one-link computation pays that input. Continuum survival,
physical calibration, full QFT structure, every group and Clay remain OPEN.

## Declaration anchors

Source prefix: `lean/YMGap/Continuum/`.

- `SU2QuaternionJumpDeterminantChannelObstruction.lean:46`,
  `jumpDeterminantChannel`; :51, `fundamentalLeaf`;
  :67, `fundamentalLeaf_heatChannel`; :76, `fundamentalLeaf_spectralChannel`;
  :85, `fundamentalLeaf_supported`; :90, `centered_channel_pin`;
  :106, `fundamentalLeaf_channel_negative_pin`; :113, `not_channel_nonnegative`;
  :123, `quadraticSource`; :128, `quadraticDeterminantSum`;
  :131, `quadraticSource_haar`; :137, `quadraticDeterminantSum_pins`;
  :145, `quadratic_nome_interpolation_fails`.
- Existing conditional theorem:
  `SU2QuaternionProductHeatChannelNomeComparison.lean:340`,
  `productChannels_nome_interpolation`, specifically its `hF` premise.
- Existing lists and sum: `SU2QuaternionProductHeatGramChannels.lean:96`,
  `productChannels`; `SU2QuaternionProductHeatPassiveChannels.lean:90`,
  `channelSum`.
- Existing original-current bridge:
  `BF4ExactSlabFixedSpatialJumpCurrent.lean:175`,
  `original_centered_current_source_pin`;
  `BF4WilsonAllNomeJumpCurrentLimit.lean:178`, `current_limit_completed_pin`.
- Existing main split: `BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:234`,
  `original_block_rayleigh_split`.

## Verification evidence

The serialized focused check exited zero. All nine printed gates depend
only on {propext, Quot.sound}; its accepted log contains no errors,
warnings, sorryAx or PANIC. Closed finite computations use `decide +kernel`,
not an external computational oracle.

The launch used fresh memory/process/swap checks and the monitored safe
launcher: one worker, 12GiB reserve and 20GiB worker ceiling. The preflight
showed 84% free memory, zero swap and no competing proof process.

| Source basename | Accepted log under /tmp | Gates | Source SHA-256 | Log SHA-256 |
| --- | --- | ---: | --- | --- |
| `SU2QuaternionJumpDeterminantChannelObstruction.lean` | `ym-jump-determinant-channel-obstruction-20261003-a.log` | 9 | `7077904a39bd272981084c14ccfe5c1a99e8c63d4b11ae5b2c9fd38d7285a766` | `9e87e76e6828c9c8cdf0515f9ee6af228866f170de1c8ea6ed28b7437a48678e` |

Root read the complete frozen source. Independent Sol read-only mathematical
review agrees with the actual-list identification, negative leaf and strict
interpolation failure; that review is not a kernel check. No older proof
module is edited. Root import is registration-only; aggregate root, full
build, broad audit/guard and progress metric were NOT run. No sorry, new
axiom, classical shortcut or resource option was introduced. CI remains
manual-only. The first canonical chart fence is unchanged, SHA-256
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
No exact displayed scaling claim closed, so no ASCII chart is reprinted.

Independent Luna final evidence/documentation QA passed the source/log
hashes, nine accepted gates, declaration anchors, unique root import,
conditional-theorem scope, unchanged first chart fence and manual-only CI.
Diff whitespace checks passed.
