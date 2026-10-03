# Original Wilson matrix tangents and the analytic meet

## Checked result and boundary

After `5351b06`, the original signed orbit derivative reaches actual scalar
matrix elements and every finite buffered Wilson word, with constructed
positive squared-error radii. Two focused checks passed 20 permitted axiom
gates. This is fixed-nome, fixed-width numerical dynamics on the SAME carrier,
not a physical clock, continuum local-field construction or full QFT closure.
The whole-project constructive Clay target remains OPEN.

## Backward construction: actual observable derivatives

`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyMatrixTangent.lean:108`
`inner_diff_right` pins the complex subtraction of original pairings.
`:115` `forward_quotient_matrix_pin` and `:132`
`backward_quotient_matrix_pin` identify the actual scalar quotients as

    reciprocal(D) * (I(y,G_(s+D)u) - I(y,G_s u)),
    reciprocal(D) * (I(y,G_s u) - I(y,G_(s-D)u)).

Here u is the input of the supplied original graph Point. Both quotients
use the SAME constructed reciprocal; the backward numerator reverses order.
No sign decision or chosen quotient representative is introduced.

`:150` `matrixElement_error_le` transports constant-one complex CS through
the actual `Completion.value`/`inner_value` map, giving

    |I(y,quotient) - I(y,slope)|^2 <= normSq(y) * epsilon.

`:171` `forward_matrix_tangent_error_le` and `:184`
`backward_matrix_tangent_error_le` use EXACTLY the original Point's orbit
radius at every signed base time. The slope is the actual -2i*Out graph
output. `:214` and `:231`, the corresponding `_unit_ball` corollaries,
give squared-error <= epsilon for normSq(y)<=1 with the SAME radius.

`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyWilsonWordTangent.lean:49`
`wordCap` multiplies the existing deliberately coarse squared character
caps of the supplied ordered representation labels. `:92` `word_norm_bound`
proves the norm bound for the ACTUAL complete word operator on the original
complex bond completion, including the empty word. No independent operator
or surrogate norm is supplied. `:110` `word_norm_unit_bound` specializes it
to unit inputs.

`:67` `wordTolerance` computes epsilon/(wordCap+1), with positivity at
`:70` and payment at `:74`. `:122` `wordMatrixRadius` evaluates the original
Point radius at this tolerance. `:147` `word_matrix_tangent_bound` returns
the BOTH-direction bounds as Type-level data. Its radius is independent of
the unit test input and numerical base time, but still depends on the
supplied Point, word, nome, width and epsilon. No state norm is inverted.
All errors are SQUARED modulus errors, not unsquared epsilon estimates.

## Forward review: the unpaid action-specific cancellation

This section records a source/planning review, not a new analytic proof.
`lean/YMGap/Continuum/BF4DyadicWilsonSquareWardMoments.lean:351`
`paddedSquare_variance` identifies v=1+m2-m1^2 with OWN variance; m2 is
the label-two character moment, NOT E[f^2]. `:359` `paddedSquare_angular`
identifies angular energy with L*(3-m2), L=4*side. `:385`
`paddedSquare_ward` and `:413` `paddedSquare_varianceRemainder` retain the
COMPLETE signed remainder R=`normalizedRemainder` and original partition/center.

Algebraic reading of those identities, with h=1-w and d=3-m2, gives

    varianceRemainder = R - h*L*(3*v-d).
    varianceRemainder <= beta*v requires
    R <= -h*L*d + (3*L*h+beta)*v.

Here beta denotes a proposed remainder coefficient, NOT the bare coupling.
The negative angular deficit must be retained when d is large relative to v.
The reviewed conditional variance inequality
`lean/YMGap/Continuum/SU2QuaternionConditionalAngularPoincare.lean:132`
`conditionalHeat_weighted_angular_variance` bounds variance ABOVE by angular
energy, not the needed upper energy bound against OWN variance. The reviewed
`lean/YMGap/Continuum/SU2QuaternionAngularBochner.lean:126`
`weighted_bochner_nonnegative` does not supply curvature for the interacting
law. These reviewed statements do not produce the missing signed bound.

The two existing consumers remain
`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`
`completed_reference_ratio` and
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`
`original_window_budget_macro_ratio`. A useful action-specific initial-energy
bound OR aggregate signed-window bound on a justified changing family remains
unsupplied. The numerical derivative branch is not a substitute for it.

## Verification and reproducibility

Accepted focused checks, both terminal exit 0, no errors/warnings/sorryAx:

- MatrixTangent: `/tmp/ym-cayley-matrix-tangent-20261003-2.log`, ten gates,
  all `{propext, Quot.sound}`. Source SHA256
  `330ee842efbc57e0b90b15277709a5876c9d9afb49388dce6e3ca579c871c22d`;
  log SHA256 `ce21d84fa965ed678fec7ce4a5656ffb0376235f0ac09c04dc7b2384930e1916`.
- WilsonWordTangent: `/tmp/ym-cayley-wilson-word-tangent-20261003-2.log`,
  ten gates; wordCap has no axioms, the other nine have only the permitted
  pair. Source SHA256
  `9ead9481ff81d2c51cd410a08443c3791705a61783180b0d90fa3203777bea68`;
  log SHA256 `257635eb8a7f36b3c75c221726fcaa024344da67da281160a53b34c3f12f5d17`.

For each leaf, from the repository root, run
`python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 12 --check-worker-limit-gib 20 --status-seconds 300 --log-file /tmp/CHOSEN.log --check lean/YMGap/Continuum/LEAF.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/LEAF.olean`.
The actual launches freshly checked processes, swap and memory pressure;
no competing compiler, zero swap and 76% reported free memory at launch.
Compiler workers were serialized and continuously monitored.

The first attempts are NOT accepted proof evidence: Matrix needed explicit
definitional closures; the two-bound word result needed `def`, since its
Type-level pair is not a proposition. Final source statements are unchanged
mathematically. Independent Sol semantic reviews and source/log QA were used.
No full root/tree build, full axiom audit, guard or metrics run is claimed.
Root imports are registration only. No sorry/axiom/frontier-field/CI change.

The canonical ASCII block is unchanged (SHA256
`6f64d1437f38622c455b8d123f001def2a5c459eebf9e785b3e40d117b19a179`),
so it was not reprinted. Nontrivial continuum survival, physical calibration,
full QFT axioms, every compact simple group and the Clay theorem remain OPEN.
