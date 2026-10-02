# Physical bond width inclusion obstruction

## Result and scope

For EVERY strict nome `0 < w < 1`, positive narrow width `n+1` and larger
width `L > n+1`, the literal inclusion of all dense Wilson sources does NOT
descend to a function between the independently constructed ORIGINAL
physical bond completions. Linearity, continuity, time intertwining and
cross-width equality of means are not assumptions of the refutation.

This rules out that full completed-carrier join, including joins starting
at widths greater than one. It does not refute controlled bulk observable
comparisons, approximate maps, thermodynamic limits or Yang--Mills itself.
The signed scaling estimate and every continuum/Clay endpoint remain OPEN.

The checked module is
`lean/YMGap/Continuum/BF4WilsonAllNomeWidthInclusionObstruction.lean`.

## Actual witness and causal argument

The explicit face is `((0,n,0,0),p01)` at narrow width `n+1`. It is retained,
but its far x0 edge has y coordinate `n+1`. The exact active-index predicate
requires that coordinate to be strictly below the width. Thus that face is
inactive without computing any growing list index. Strict padding makes
the SAME face fully active in the larger carrier.

The rational source is the raw plaquette minus its one-step advance:
`d = x - advance 1 x`. No interacting mean appears in this syntax.
`timeDefect_source_zero_iff` proves its actual physical bond class is zero
exactly when the ORIGINAL time map kills the OWN-centered one-step source.
For the forward implication, nullity gives `T x = T^2 x`; its centered
one-step image is a fixed vacuum-complement vector, hence zero by the
existing strict completed two-step bound. The reverse implication uses
the computed vacuum projection, which time fixes.

At the narrow width the existing inactive-face theorem kills that centered
image, so `ofSource d = ofSource zero`. At the larger width the existing
strictly positive original response floor excludes this equality. Literal
inclusion preserves the ordered plaquette, difference and advance, so it
sends the narrow d to precisely this nonnull larger source. Any proposed
function preserving EVERY `ofSource` would send the same narrow class to
both larger zero and larger nonzero: contradiction.

| Declaration | Source line | Exact claim |
| --- | --- | --- |
| `source_eq_zero_iff_time_kernel` | `BF4WilsonAllNomeWidthInclusionObstruction.lean:99` | Completed physical source nullity iff ORIGINAL one-step kernel. |
| `timeDefect` and `embed_timeDefect` | `BF4WilsonAllNomeWidthInclusionObstruction.lean:115`, `:118` | Literal rational difference and its actual completed defect. |
| `timeDefect_source_zero_iff` | `BF4WilsonAllNomeWidthInclusionObstruction.lean:126` | Physical defect nullity iff OWN-centered one-step image is zero. |
| `boundaryFace_mem` and `boundaryFace_not_fully_active` | `BF4WilsonAllNomeWidthInclusionObstruction.lean:159`, `:168` | Retained boundary face with an inactive far edge, at every positive width. |
| `boundarySource` and `boundary_timeDefect_source_zero` | `BF4WilsonAllNomeWidthInclusionObstruction.lean:178`, `:182` | Explicit narrow rational source with zero physical defect class. |
| `active_plaquette_timeDefect_source_ne_zero` | `BF4WilsonAllNomeWidthInclusionObstruction.lean:191` | Fully active face has nonzero physical defect class. |
| `inclusion_plaquetteSource` | `BF4WilsonAllNomeWidthInclusionObstruction.lean:210` | Actual unchanged ordered face under literal dense inclusion. |
| `included_boundary_timeDefect_source_ne_zero` | `BF4WilsonAllNomeWidthInclusionObstruction.lean:219` | EVERY strict enlargement makes this included defect nonnull. |
| `no_completed_literal_inclusion` | `BF4WilsonAllNomeWidthInclusionObstruction.lean:232` | No arbitrary function preserving ALL dense sources, for any `n+1 < L`. |

Every abbreviated filename in this table is under `lean/YMGap/Continuum/`.
The full parameter range is in the declarations, not a hypothetical
certificate of existence. No analytic hypothesis or frontier field is added.

The checked dense-to-union chart arrow is not this refuted map:
`BF4WilsonSpatialUnionNaturalTransformation.denseToUnion`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionNaturalTransformation.lean:91`)
maps RAW expressions into ONE separately constructed common completion under
its stated small-nome premises. `UnionCompletion`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionSeminorm.lean:139`) is a quotient
of staged Cauchy streams, not of each independent physical bond completion.
That arrow does not assert descent through the null classes refuted here.

## Verification

Final focused check on 2026-10-02 UTC exited 0 without warnings or errors:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4WilsonAllNomeWidthInclusionObstruction.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeWidthInclusionObstruction.olean --log-file /tmp/ym-width-inclusion-obstruction-20261002-final.log
```

All thirteen printed gates passed: `boundaryFace` has no axioms; the other
twelve use exactly `{propext, Quot.sound}`. No `sorryAx`, classical choice,
custom axiom, native proof oracle, witness erasure or weakened field.
Independent Sol mathematical/source review and Luna scope/evidence review
passed. Machine pressure reported 86 percent free before and after checks;
swap stayed at zero. No competing compiler, test suite or runner was found.
The monitored launcher used one 20 GiB capped worker and a 12 GiB OS reserve.

- Source SHA256: `cb4042dac0d908b6a26233752d96543166ed6bc5214a7dcf222f0d8bf93b5ed9`.
- Final log SHA256: `eb37fcb585a492de6d56f41abc55cd648b5b81080a01fd0fe78fa702e67f82fd`.
- One root import added. Full root/tree build, full audit, guard and progress
  runs were NOT performed. The final focused check is the verification scope.
- Automatic CI remains disabled; its retained workflow permits manual dispatch.
- Canonical chart block unchanged: SHA256
  `6f64d1437f38622c455b8d123f001def2a5c459eebf9e785b3e40d117b19a179`.
  No exact displayed claim closed and no ASCII chart was reprinted.

## Redirected next frontier

Do not construct a full cross-width physical map by syntactic inclusion:
its null relation is now explicitly refuted at every positive base width.
Instead retain the original sources and pairings on strictly padded bulk
families and prove quantitative volume/spacing comparisons before any
quotient or limit join. This is an OPEN task, not a proved replacement map.
The primary complete signed energy/OWN-variance estimate on a justified
changing family remains OPEN, as do physical mass calibration, nonzero
continuum survival, full same-theory QFT and every-group realization.
