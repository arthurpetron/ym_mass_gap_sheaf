# Original Wilson word fourth moment

Date: 2026-10-01 UTC. The selected-link fourth moment now bounds the whole
ordered Wilson word under the SAME original edge density. It pays the
quartic correction in the existing radial energy inequality. The mixed
radial moment, its comparison with centered variance, and physical scaling
remain open. This is finite SU(2) progress, not continuum or Clay closure.

## Actual bound and parameter dependence

Let h=1-w, let L be the literal number of edges in an active physical source
loop, and retain the previous explicit budget

    B(w,S) = 296*h^2 + 32*(S+2)^4*h^4 + 80*S^3*w^(S^2).

Write r=|U_lower-U_upper|^2 for the two ordered word quaternions and Z for
the original odd partition. The checked result is

    H[edgeDensity * r^2] <= 16*L^4*B(w,S)*Z.

`BF4ExactSlabFixedSpatialWilsonQuarticIncrement.word_quartic_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonQuarticIncrement.lean:62`)
has guards 0<w<1, S>=1, K>=S+3, headCutoff(w)<=K,
1<=2*w^(4*(S+2)), w^(S*S)<=1/8, and EVERY loop occurrence active.
The `SourceLoop` supplies physical membership. Repetitions and overlapping
variables are allowed. No independence is assumed.

There is no extra width, depth or cutoff constant, but length dependence
is explicit. A growing loop must pay L^4; the estimate is not uniform in
width along arbitrary growing-loop families. Nome and split dependence
remain explicit in B. No physical time or justified scaling law is supplied.

## Proof on the original carrier

`QuaternionHaarWordComponents.terms_components`
(`lean/YMGap/Continuum/QuaternionHaarWordComponents.lean:87`) proves the
literal replacement telescope in all four quaternion coordinates. Factors
are never commuted. Haar-unit prefix and suffix norms cancel only under
arbitrary insertions; their squared-norm equality can therefore be squared.

`QuaternionHaarWordQuartic.scalar_fourth_certificate`
(`lean/YMGap/Continuum/QuaternionHaarWordQuartic.lean:63`) constructs a
supported-square certificate for L^3*sum(p_i^4)-(sum p_i)^4. It combines
two finite Cauchy certificates using the difference-of-squares identity.
Applied coordinatewise, followed by four-coordinate Cauchy, it gives the
conservative factor 16*L^4 in `word_norm_quartic_bound`
(`lean/YMGap/Continuum/QuaternionHaarWordQuartic.lean:413`).
This polynomial constant is not asserted optimal.

`BF4ExactSlabFixedSpatialLinkQuartic.selected_quartic_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLinkQuartic.lean:173`)
identifies each oriented link's chordal square with the original relative
heat defect and reinserts the selected heat factor into the complete edge
density. Both original endpoint sources and every spectator factor remain.
The previous quartic estimate supplies all analytic inputs; no source or
variance hypothesis was added to obtain the word bound.

## Original energy consumer and remaining input

For f=2*scalar(U_lower), put M=H[edgeDensity*r*(4-f^2)].
`radial_moment_split`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonQuarticIncrement.lean:92`)
is an exact integral identity. It gives the checked bound

    2*energy <= 2*M + 2*(16*L^4*B(w,S)*Z)

in `wilson_energy_radial_quartic_cleared`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonQuarticIncrement.lean:109`).
M is not factored into separate expectations. The remaining source-relative
inequality is not inferred from partition control.

The parallel source review found a possible signed-source polarization for
M, but its vector cross response is not scalar centered variance. That
polarization is not implemented or claimed proved. The strategy review in
`audits/RESEARCH-TARGETED-YM-FRONTIER-2026-09-30.md` instead prioritizes a
specified signed observable family and the existing exact Ward/Taylor
identity, including its entire signed remainder. A useful estimate must
reach E_j<=M0*tau_j*Var_j for the SAME observable and actual physical time.
Neither a fixed microscopic source nor a growing/smeared family is already
proved to satisfy that input. No new conditional survival package is added.

## Verification and scope

Four final focused checks passed 21 printed axiom gates, all within
{propext, Quot.sound}; four gates were axiom-free. No sorry, new axiom,
Classical dependency, native_decide, noncomputable declaration or canonical
field change was introduced. Intermediate namespace/elaboration errors were
fixed before accepting any check. Only the main agent ran the compiler.

Checks were serialized through the safe launcher with one worker, a 20 GiB
ceiling and 12 GiB OS reserve. Preflight found no competing compiler/runner;
memory queries reported 89--90% free. No full root build, full-tree audit or
guard was run. Root imports were added but not compiled as an aggregate.
The canonical chart is unchanged and was not reprinted. Automatic CI remains
off; the existing workflow has only a manual dispatch trigger.

Final log SHA-256 values, under `/tmp/`:

- `ym-word-components-20261001.log`:
  `44daa76cb2d495d21f97a435e85607e111a31dab10d3ba6d7997e16b72873abe`.
- `ym-word-quartic-20261001.log`:
  `6f61a7b2bc8bdb67ccb41ed74f517a021413505ccb5d25e58605936194916f93`.
- `ym-link-quartic-20261001.log`:
  `d23053d6afd2c994b2fd4eb96c3cee1070f85521c576a01410086645515dc96c`.
- `ym-wilson-quartic-20261001.log`:
  `85dbd46419e52848c74fdd3cccf48279a24fcbc9508e0f9e09f9c07dec62d296`.
