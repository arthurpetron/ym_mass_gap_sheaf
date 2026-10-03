# Sharp original one-step gap and necessary filtered-rate compatibility

The whole-project continuum Yang--Mills/Clay target remains OPEN. This
checkpoint sharpens an inhabited finite-parameter operator estimate and
connects it to a necessary condition on the actual pending signed budget.
It does NOT construct that budget or a justified scaling family.

## Mathematical increment

Use the EXISTING original all-nome Wilson completion, inner product B,
physical one-step time map T and vacuum U. Put

    q = mixRate(w,width), e = mixFraction(w,width) = 1-q.

The original two-step rate is LITERALLY q*q, not an opaque independently
chosen constant. Its completed bound gives ||T*x||^2 <= q^2*||x||^2 for
every x orthogonal to U. For q>0, expand the SAME completed norm:

    0 <= ||q*x-T*x||^2
       <= 2*q^2*||x||^2 - 2*q*B(x,T*x).

Only the strictly positive rational 2*q is cancelled. This proves
B(x,T*x) <= q*||x||^2. For q=0, the squared norm bound and original
positive definiteness give T*x=0; no injectivity or positive input norm
is assumed. These two branches cover the full [0,1) rate interval.

The exact one-step defect margin is consequently

    e*||x||^2 <= B(x,x)-B(x,T*x).

The margin e is the original kineticFloor/kineticCap fraction, still
nome- and width-dependent. This is stronger than the older coefficient
(1-q^2)/2; no old declaration, graph field or frontier predicate is changed.

Apply the bound to the SAME smoothed state T^t*x. Vacuum orthogonality is
preserved by the original time map. With R_j=B(x,T^j*x), the exact translated
identity gives R_(2t+1)<=q*R_(2t), and hence

    e*R_(2t) <= R_(2t)-R_(2t+1).

On the EXISTING dyadic unit excitation, every R_(2t) has its already
constructed strictly positive floor squareResponseFraction^(2t). This floor
is used only for pointwise cancellation; it is NOT a uniform scaling reserve.
For any rational m>=0 and C, a supplied budget on this actual response

    m*(R_(2t)-R_(2t+1)) <= C*R_(2t)

therefore NECESSARILY satisfies m*e<=C. In particular, choosing m=s=2t
forces s*kineticFloor/kineticCap<=C on every proposed family sample.
It is a necessary compatibility test, not a sufficient survival theorem.

The same constraint follows from the literal original finite scalar budget
for every stage k>=a supplied start. The previous checked OWN-centered cost
and variance limits reach N*(R_(2t)-R_(2t+1)) and N*R_(2t), respectively.
Existing generic eventual-order passage permits the late-stage premise;
no estimate at the early cutoff is required. The original positive norm N
is cancelled using its existing starRatio floor. Both finite chronological
partitions, actual moving OWN mean and normalization remain unchanged.

Finally, the already inhabited regularized-log graph consumes the sharper
margin at its original input T*x:

    e*||T*x||^2 <= B(T*x,regularizedLog(x)).

This is a SAME graph-core bound at fixed nome/width, not identification of
that graph with the physically calibrated continuum Hamiltonian.

## New declaration map

All namespaces match the filenames under YMGap.Continuum.

| Declaration | Source | Exact role |
| --- | --- | --- |
| `completed_oneStep_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeOneStepGap.lean:94` | Exact q form bound on every original completed vacuum-orthogonal state, including q=0. |
| `completed_even_filtered_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeOneStepGap.lean:145` | SAME-state even-horizon response bound; no odd-start extension is claimed. |
| `completed_oneStep_defect_margin` | `lean/YMGap/Continuum/BF4WilsonAllNomeOneStepGap.lean:159` | Exact kinetic floor/cap lower margin for the original one-step loss. |
| `dyadicUnitResponse_even_filtered_lower` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredRateConstraint.lean:93` | Instantiates the lower loss bound on the existing normalized dyadic response. |
| `filtered_budget_rate_constraint` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredRateConstraint.lean:108` | Supplied SAME-response budget necessarily has m*mixFraction<=C. |
| `originalOwnBlock_budget_rate_constraint` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredRateConstraint.lean:131` | Literal late-stage finite budget implies the same constraint through its checked cost/variance limits. |
| `core_form_gap_sharp` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:133` | Exact margin reaches the existing regularized-log graph input, without changing old fields. |

## Verification boundary

Three accepted serialized focused checks passed 16 unique printed gates:
seven new declarations and nine unchanged gates in the modified LogCoreGap
module. Every gate has exactly {propext, Quot.sound}; accepted logs have no
errors or warnings. Independent source/semantic review passed. No new sorry,
axiom, analytic hypothesis bundle, classical shortcut, guard weakening or
surrogate carrier was introduced. No full build/audit ran; root imports are
registered only, NOT aggregate-checked. CI remains off.

Each launch refreshed dynamic capacity and used one monitored worker, a
20-GiB worker ceiling and 12-GiB OS reserve. Preflight free memory was 85--86%,
swap was zero, and no competing compiler/test/runner process was present.
Earlier unsuccessful mechanical checks are NOT accepted proof evidence.

Accepted source SHA256:

- `BF4WilsonAllNomeOneStepGap.lean`: `8c9e574e9510118dd190768ab82663b92c7fbea5d50c2947cf158092beb078f3`
- `BF4WilsonAllNomeDyadicFilteredRateConstraint.lean`: `e77388367d1e45f002abde3e0ba6a5e32bc266d0b2580ddcede0074f125a0e42`
- `BF4WilsonAllNomeLogCoreGap.lean`: `6e8eeaf7efce0f820d704bb0c36e59176136ae3e5017315dc9ce5931bfebd1fd`

Accepted local logs and SHA256:

- `/tmp/ym-allnome-one-step-gap-20261003-d.log`: `88cd3b58818b6f17cd9e0c6199a6a76281bba30dc9c7b27b8148190f116f36fe`
- `/tmp/ym-allnome-filtered-rate-20261003-b.log`: `8f10fe37cf075155ba535533b963e273f3237ea0048e07a39bde20180019dec2`
- `/tmp/ym-allnome-log-core-sharp-20261003-a.log`: `15d6e8764c3a1e1b9eb0a6100624b109f3cd3eb2af0365d8b7ccdc4a8398aca6`

## Open producer and next mathematical work

The finite relative signed upper bound remains unpaid. Moment positivity and
late filtering alone bound the cost ABSOLUTELY, not relative to its surviving
norm. This new lower bound does not reverse that inequality. A changing-family
candidate must pass the necessary rate constraint AND produce a useful upper
estimate or the existing direct SAME macroscopic ratio; satisfying the constraint
alone is insufficient. No physical trajectory is supplied here.

The full combined original energy/commutator, cross-scale relative comparisons,
spatial/spacing control, continuum survival, physical mass calibration, full
SAME-theory QFT and every compact simple group remain OPEN. The canonical
displayed claims did not change, so no ASCII chart is reprinted.
