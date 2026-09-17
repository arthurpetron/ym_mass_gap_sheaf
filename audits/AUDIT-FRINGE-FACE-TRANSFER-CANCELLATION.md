# Original fringe-face transfer and connected-correlation cancellation

Date: 2026-09-17 21:50 UTC. Parent checkpoint:
`e50121233034ad5ef4ac1c26a1f9e1f1a7de4da6`.

Whole-project goal: constructive nontrivial continuum Yang--Mills on R^4
for each compact simple group, with the required same-theory QFT properties,
isolated vacuum and strictly positive finite physical Hamiltonian mass gap.
The whole-project goal remains OPEN.

## Result and actual consumer

Let T be the ORIGINAL fixed-spatial transfer K(V*.), g_m=T^m(1), and p a
physical spatial plaquette with an inactive fringe link. Set c=coeffW(w,1),
the literal fundamental heat coefficient 2*w^3. For every supported test s,
every rational w and every K>=1, the checked identity is

    H[s*T(g_m*chi_p)] = c*H[s*Tg_m].

The two messages are the actual observed/unobserved pair identified in
`AUDIT-TRANSFER-ORBIT-CONSUMER.md`. No factor of V or g_m is replaced.
The equality is Haar-tested, not free-polynomial coefficient equality.

Writing m(f)=H[V*f], weighted symmetry then gives, for every r>=0,

    m[s*T^(r+1)(g_m*chi_p)] = c*m[s*g_(m+r+1)].

The original finite-window joint and marginal ratios consequently satisfy

    expectation(chi_p * q_at_gap) = c*expectation(q_at_gap),
    expectation(chi_p) = c,
    connected(chi_p, q_at_gap) = 0,              gap = r+1.

The final theorem directly names the existing `windowRatio`, with the
same total window, boundaries, action and positive partition in all three
terms. The right endpoint probe q is arbitrary, supported and signed.

## Causal proof

1. Character recurrence gives chi_1*chi_(j+1)=chi_(j+2)+chi_j. At a face
   link independent of the complete spectator, positive characters integrate
   to zero. Thus only j=1 survives in the complete heat-prefix pairing with
   chi_1; every higher term is cancelled before summing.
2. The existing explicit `FringeFaceLeaf` has a link unique among ALL
   original spatial faces. Direct induction on the physical nodup face list
   retains every other factor in the spectator. No erasure/permutation lemma
   with a classical dependency is imported.
3. Move the kinetic map onto the arbitrary output test by its actual Haar
   symmetry. That image and every g_m omit inactive coordinates. The full
   spectator is therefore eligible for step 1. The original vacuum heat
   removal identity restores the same denominator action.
4. Move later transfers onto the supported test using the original
   V-weighted symmetry. The physical tested equality is not passed to a
   coefficient-congruence lemma. Coefficient congruence is used only for
   the genuine zero-window presentation identity.
5. Existing separated-window pins use one partition Z and reciprocal z.
   The joint numerator is c*C and the left numerator is c*Z. Thus the
   normalized joint is c*C*z, left marginal c, and right marginal C*z.
   Only Z is inverted; connected cancellation is exact.

## Declaration map

All paths below start at `lean/YMGap/Continuum/`.

| Declaration | Source | Scope |
| --- | --- | --- |
| `character_pair_moment` | `BF4ExactSlabFixedSpatialFaceHeatMoment.lean:57` | Every spin with the same supported one-link-independent spectator. |
| `heatFace_character_moment` | `BF4ExactSlabFixedSpatialFaceHeatMoment.lean:149` | Full prefix at every K>=1; arbitrary rational nome. |
| `spatial_fringe_face_moment` | `BF4ExactSlabFixedSpatialFringeFaceTransfer.lean:133` | Entire original spatial action retained. |
| `inactive_fundamental_transfer_pair` | `BF4ExactSlabFixedSpatialFringeFaceTransfer.lean:155` | Actual T, actual g_m, arbitrary supported Haar test. |
| `inactive_fundamental_iterate_pair` | `BF4ExactSlabFixedSpatialFringeFaceCorrelations.lean:75` | Every positive separation in the original weighted pairing. |
| `inactive_input_numerator` | `BF4ExactSlabFixedSpatialFringeFaceCorrelations.lean:139` | Same two boundaries, arbitrary supported endpoint probe. |
| `inactive_input_partition` | `BF4ExactSlabFixedSpatialFringeFaceCorrelations.lean:153` | Left numerator is c times the original unobserved partition. |
| `window_connected_zero` | `BF4ExactSlabFixedSpatialFringeFaceCorrelations.lean:166` | Exact zero connected covariance in the existing normalized window law. |

Existing geometric inputs are `fringeFaceLeaf`,
`BF4ExactSlabFixedSpatialFringeFaceGeometry.lean:165`, and
`spatialFaces_nodup`, `BF4ExactSlabFixedSpatialFacePlacement.lean:172`.
Terminal independence is `terminal_fringe_independent`,
`BF4ExactSlabFixedSpatialFringeProjection.lean:97`.
The scalar coefficient is `BondMovingStep.coeffW`,
`BondMovingStep.lean:259`, specialized to label one.

## Boundaries and next mathematical work

Raw identities use K>=1 but no positivity or restriction on rational w.
The normalized theorem additionally retains 0<w<1 and the existing
headCutoff(w)<=K positivity guard. All widths, both terminal depths and
positive temporal gaps are quantified. Width zero admits no physical face;
the theorem makes no nontrivial claim there.

The face must NOT be fully active. The exact elimination does not apply
to the fully active cubical core: the required private inactive link is
absent there. It also does not establish the same formula for products of
boundary insertions sharing that link. Gauge-invariant Wilson products,
arbitrary spins and the full dense sector are not silently covered.

Inactive-face membership depends on width. This is not a fixed-observable
thermodynamic or continuum-limit theorem and is not evidence for a nonzero
completed excitation. It removes a finite boundary contribution from the
actual iterated connected quantity. The next target is a quantitative
same-partition bound for the retained active face/core pair, with the
regulator and coupling control required by the scaling route.

The small-nome completed gap/excitation remain unchanged. Improved-domain
limiting-form construction, physical mass calibration, same-theory continuum
QFT and every compact simple group remain open. No canonical frontier field
or analytic guard is weakened and no new analytic premise is added.

## Verification

Three final focused checks passed through the monitored launcher, serialized
at one worker with a 20 GiB ceiling and a fresh process/swap preflight for
each check. All eight public printed axiom gates are within
{propext, Quot.sound}; final logs have no errors, warnings or sorryAx.
The safe-build skill kept verification focused and serialized. Initial
development errors were a nonexistent distributivity lemma, an incorrectly
qualified support lemma, and a parenthesization error; no resource limits
or proof statements were changed to repair them.

Independent read-only mathematical review passed the complete-spectator
selection, original first-pair identity and all-separation same-partition
consumer. Three semantic-root imports were added; root/full-tree/full audit,
guard and progress runs were NOT performed. CI remains manual-only. No
sorry was introduced or discharged, and no classical axiom was used.

| Final log | SHA-256 |
| --- | --- |
| `/tmp/ym-fixed-spatial-face-heat-moment-20260917.log` | `ef701ecd4bf0b93553063c7037c470a40e3c93382fbde6fe2e7b5b29ed5dadaa` |
| `/tmp/ym-fringe-face-transfer-20260917.log` | `99c05ace9955d1dd26bc1131cc36d23787fca4cd76136467428aeb4dbc3d8ba5` |
| `/tmp/ym-fringe-face-correlations-20260917.log` | `1715e51df670e8c760f5e792a26a961e17b70e0ab4b72a34684238af6913660e` |
