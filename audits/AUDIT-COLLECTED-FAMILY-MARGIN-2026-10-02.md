# Collected ORIGINAL terminal iteration and finite-margin evaluator

## Outcome and actual consumer

PROGRESS after `6f05511`: the finite exponent universe now bounds an ACTUAL
computed sparse representation. The new terminal iterator combines equal
monomials before each subsequent step, preserving every coefficient probe
of the ORIGINAL iteration. The complete original edge retains BOTH terminal
factors, all kinetic/spatial factors and the joint spectator projection.

`terminal_length` bounds stored message length at every depth by a list from
cutoff and spatial width. `numerator_length` bounds each of the six collected
margin numerators by the existing list from cutoff and family length, not
width, depth, nome or signed coefficients. This is not a coefficient-size,
intermediate-work or feasible-runtime bound.

The alternative `check` has exactly the ORIGINAL acceptance conditions.
`check_correct` proves equivalence with
`BF4WilsonAllNomeFiniteReferenceMargin.check`
(`lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:267`).
`certify` computes an `Option` of that EXISTING original `Certificate`
(same file, line 274): success carries the tolerance, pivot and acceptance
proof as data; failure is `none`. No successful useful-margin instance has
been computed or asserted.

## Checked mathematical chain

| Declaration | Source | Scope |
| --- | --- | --- |
| `collect_coeff` | `lean/YMGap/Continuum/SU2QuaternionSparseCoefficientCollector.lean:118` | All monomial-weighted coefficient probes unchanged. |
| `collect_keys`, `collect_nodup`, `collect_nonzero` | same file, lines 159, 190, 225 | No new exponent key; distinct keys; zero coefficients removed. |
| `collect_length_le_cover` | same file, line 242 | Actual collected length bounded by any finite key cover. |
| `terminal_coeff` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCollectedFamilyMargin.lean:120` | Coefficient equality to the original terminal at every depth. |
| `terminal_length` | same file, line 138 | Length <= `monomials (N width) (fun _ => K)`.length. |
| `numerator_length` | same file, line 220 | All six actual collected insertions bounded by `marginMonomials K qs.length`.length. |
| `pairing_pin` | same file, line 250 | Exact equality to original compressed Haar pairing. |
| `finite_margin_pin` | same file, line 298 | Exact original reference-margin input, with actual cutoff/padding. |
| `check`, `check_correct`, `certify` | same file, lines 324, 332, 348 | Computed acceptance and existing original certificate data. |

The collector uses exact exponent-list equality, rational addition and a
zero-numerator test. It is a deterministic first-match list collector, not
an indexed/hash-map complexity result or reduction modulo sphere relations.
Key provenance proves literal support/degree preservation. Distinct keys and
the already proved finite covers yield the representation-length ceilings.

The original finite `step` integrates the input slice. Its retained degree
ceiling comes from the kinetic kernel. Collection preserves this ceiling;
no degree statement is transported through arbitrary coefficient equality.
Full coefficient equality instead transports the SAME action through BOTH
edge endpoints, joint projection, exponent compression and Haar evaluation.
The normalized moments keep the original positive partition. OWN centering
and the COMPLETE signed jump square are unchanged.

At a reference depth `s+1` and cutoff `headCutoff w+pivot`, the new checker
keeps `0<=c`, `0<epsilon`, the ORIGINAL `referenceCutoff ... epsilon<=pivot`
and `epsilon+epsilon<=margin`. Neither the modulus nor the slack is weakened.

## Parameters and honest boundary

Algebraic recurrence and length bounds quantify over arbitrary rational nome
and finite cutoff/width/depth. Terminal length depends on cutoff AND width;
numerator length depends on cutoff AND family length. Face membership is
explicit. Positive normalized evaluation retains `0<w<1` and
`headCutoff w<=K`; the checker additionally retains the original physical
padding `base<width` and face-membership hypotheses.

The terminal is collected DURING iteration. The central edge and projected
numerator are still formed before their final collection. Coefficient bit
sizes, intermediate expansion, work per operation and feasible runtime remain
unbounded. Finite-list size can be enormous; no allocation or practicality
claim follows from these bounds. No all-cutoff finite universe is asserted.

This constructs an alternative exact evaluator, not positive accepted data,
a signed variance-relative estimate, a changing-family rate, cross-scale
identification, continuum survival, physical mass, QFT axioms, every-group
realization or the Clay theorem. All those physical endpoints remain OPEN.

## Focused verification

Both changed files passed serial `scripts/safe_lean_build.py --jobs 1`
checks with `--check-worker-limit-gib 20` and their matching `--check-output`
under `lean/.lake/build/lib/lean/YMGap/Continuum/`:

- `/tmp/ym-sparse-collector-20261002-final.log`: EXIT 0, eleven public gates.
- `/tmp/ym-collected-family-margin-20261002-final.log`: EXIT 0, twenty-eight gates.

All 39 gates lie within {propext,Quot.sound}; `insertKey` and `collect` are
axiom-free. Accepted logs contain no errors, warnings or sorryAx. Failed draft
logs are NOT evidence. No new sorry, axiom, classical/native oracle, analytic
premise, erased witness or weakened frontier was introduced.

Sol independently reviewed the SAME-object mathematics: PASS. The independent
checker review confirmed exact original cutoff/slack/coupling/depth/padding
and Type-valued existing certificate output: PASS.
Luna independently checked all hashes, declaration citations, 39 gate entries,
documentation scope and byte-identical canonical chart fences: PASS.

Live pre/post memory-pressure-free readings were 85%/84%; post-check swap was
zero and no compiler/runner survived. ONE 20-GiB worker and the 12-GiB reserve
were unchanged. One root import added. Full root/tree build, audit, guard and
progress-metric script NOT run. CI and canonical chart fences unchanged;
no ASCII reprint.

| Artifact | SHA-256 |
| --- | --- |
| `SU2QuaternionSparseCoefficientCollector.lean` | `5cdf8e1d0bdd08fb5f3758cb46bc708fcefe36f05ee4c66d42ac65190c49ea9c` |
| `BF4ExactSlabFixedSpatialCollectedFamilyMargin.lean` | `2b06e176437ed7b6b33f75a7ea16f1e12679eb517e9802dcf770138cffffd0bd` |
| `/tmp/ym-sparse-collector-20261002-final.log` | `5677847d1ee6abf868e947e22367867de64bb16b0eb452e3a6f800fa547967f6` |
| `/tmp/ym-collected-family-margin-20261002-final.log` | `4a9b618f78e4972dddf61a67bb405c0809da7ccab564186361896cc2259cd08e` |

## Repointed frontier

NEXT: evaluate/estimate actual ORIGINAL joint moments with useful positive
signed slack on a justified changing family, using the exact collected
evaluator as one computation tool. The signed Ward/Taylor remainder has no
new favorable-sign or variance-relative bound here. Do not replace it by
degree/term-count control or by an assumed positive matrix direction.
