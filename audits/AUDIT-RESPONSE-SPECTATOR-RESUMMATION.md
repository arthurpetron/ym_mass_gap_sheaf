# Original response: exact spectator resummation and local normalization

Date: 2026-09-16 (America/Los_Angeles). Base: `284e8fa`.

PROGRESS: detached response selections are exactly resummed, and their
normalization has a constructed local collar cost. OPEN: a spatially
decaying estimate on the remaining original signed sum with useful
coupling/scale dependence. No canonical frontier atom is closed.

The whole-project goal remains constructive continuum Yang--Mills on R^4,
the required QFT axioms, and a positive physical Hamiltonian gap for every
compact simple gauge group, with all clauses pinned to the same theory.

## 1. Exact argument and actual consumer

For the original old action S and inserted heat face f, write

    C_S(p,q) = M_S(pq) Z_S - M_S(p) M_S(q)
    R_S      = C_(S+f) Z_S^2 - C_S Z_(S+f)^2
    D_S      = Z_(S+f)^2 Z_S^2.

These are the existing cleared response and denominator, not a new law:
`BF4ExactSlabConnectedFaceResponse.response_identity`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:90`, and
`BF4ExactSlabConnectedFaceResponse.responseDenominator`, same file:73.

When S=A++B is a literal disjoint core/spectator split and both probes
and f lie on the A side, each connected numerator acquires Z_B^2 and
each endpoint partition acquires Z_B. Thus

    R_(A++B) = R_A Z_B^4,       D_(A++B) = D_A Z_B^4.

The existing finite Mobius coefficients factor across that same split.
Grouping selections by their computed rooted core uses the already-proved
spectator-fiber permutation. Mobius reconstruction sums all spectators
exactly, without absolute values, into their original partition fourth power:

    R_S = sum_A responseCoefficient(A) * Z_detached(A,S)^4.

Here A ranges over computed rooted anchors passing the three existing
mark-separation tests. The root includes both probe supports AND the
inserted face's links. No spectator factor is discarded or replaced by 1.

| Declaration | Source | Role |
|---|---|---|
| `BF4ExactSlabResponseSpectatorFactorization.partitionFourth` | `lean/YMGap/Continuum/BF4ExactSlabResponseSpectatorFactorization.lean:46` | Literal original partition fourth power. |
| `BF4ExactSlabResponseSpectatorFactorization.response_spectator_factorizes` | `lean/YMGap/Continuum/BF4ExactSlabResponseSpectatorFactorization.lean:108` | Exact signed numerator factorization. |
| `BF4ExactSlabResponseSpectatorFactorization.denominator_spectator_factorizes` | `lean/YMGap/Continuum/BF4ExactSlabResponseSpectatorFactorization.lean:148` | Same factor in the two-endpoint denominator. |
| `BF4ExactSlabResponseSpectatorFactorization.responseCoefficient_spectator_factorizes` | `lean/YMGap/Continuum/BF4ExactSlabResponseSpectatorFactorization.lean:167` | Finite differences factor before bounds. |
| `BF4ExactSlabRootedFunctionalResummation.rooted_functional_resummed_expansion` | `lean/YMGap/Continuum/BF4ExactSlabRootedFunctionalResummation.lean:55` | Reuses the existing rooted selections and fiber bijection for a general factoring functional. |
| `BF4ExactSlabRootedResponseResummation.markedLinks` | `lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:48` | Actual three-mark root. |
| `BF4ExactSlabRootedResponseResummation.rootedResponse` | `lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:57` | Signed sum with its anchor-dependent detached action. |
| `BF4ExactSlabRootedResponseResummation.response_resummed_filtered` | `lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:66` | Exact equality to the original response; all generic factorization premises are proved. |
| `BF4ExactSlabRootedResponseResummation.covariance_response_bound_of_rooted` | `lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:118` | A SUPPLIED eventual bound on the signed sum controls the same original cutoff-limit covariance difference. |

That last theorem uses the existing analytic consumer
`BF4ExactSlabConnectedFaceResponse.covariance_response_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:224`.
It preserves both endpoint partitions and the existing constructive limit
moduli. It does not establish the quantitative hypothesis it consumes.

## 2. Constructed normalization cost

Let h=headFloor(w), let c be the number of collar faces removed to leave
the actual detached action, and set

    collarFloor(w,c) = (h^c*h^c)*(h^(c+1)*h^(c+1)).

At every rational 0<w<1 and K>=headCutoff(w), the existing positive
retained-head certificate restores each removed face with a factor h.
The old partition restores c faces; the new partition restores c+1,
including f. Squaring and multiplying gives the proved comparison

    collarFloor(w,c) * Z_detached^4 <= D_S.

This is `BF4ExactSlabResponseCollarNormalization.detached_fourth_floor`,
`lean/YMGap/Continuum/BF4ExactSlabResponseCollarNormalization.lean:106`.
The actual shared-link background remains in both comparisons.
The underlying estimate is
`BF4ExactSlabRetainedHeatHeadComparison.headProduct_weighted_floor`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:186`.

The existing literal incidence count bounds c by

    N = 6*(roots.length + 4*anchor.length).

See `BF4ExactSlabCollarDegreeBound.collarIds_length_le`,
`lean/YMGap/Continuum/BF4ExactSlabCollarDegreeBound.lean:78`.
The new explicit data and consequences are:

| Declaration | Source | Content |
|---|---|---|
| `BF4ExactSlabResponseCollarNormalization.collarFloor` | `lean/YMGap/Continuum/BF4ExactSlabResponseCollarNormalization.lean:47` | Positive floor with the inserted face counted twice in the new partition square. |
| `BF4ExactSlabResponseCollarNormalization.collarCost` | `lean/YMGap/Continuum/BF4ExactSlabResponseCollarNormalization.lean:60` | Constructed positive reciprocal of that floor, not an opaque constant. |
| `BF4ExactSlabResponseCollarNormalization.collarCount` | `lean/YMGap/Continuum/BF4ExactSlabResponseCollarNormalization.lean:156` | Explicit marked-support/core-size count N. |
| `BF4ExactSlabResponseCollarNormalization.detached_fourth_bound_bounded_count` | `lean/YMGap/Continuum/BF4ExactSlabResponseCollarNormalization.lean:174` | Z_detached^4 <= collarCost(w,N)*D_S. |
| `BF4ExactSlabRootedResponseResummation.rooted_response_term_bound` | `lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:94` | Absolute value of the actual resummed term <= (abs(coefficient)*collarCost(w,N))*D_S. |

The cost depends on w and on the marked-support/core sizes, with the
cutoff guard explicit. It has no ambient-volume parameter; the bound
avoids a reciprocal floor over all ambient faces. This does NOT make
it uniform when the marked support or core grows. There is no claim
that the cost is small, that it yields a summable series, or that it
is uniform in the coupling. No physical lattice-spacing rate is given.

## 3. Scope, parallel work and open residue

- The finite resummation identity holds for arbitrary rational w and
  cutoff K. Its normalization estimate has the additional positive-nome,
  late-cutoff and physical-face guards written above.
- Ambient enumeration is duplicate-free. There is no id-not-in-ambient
  premise: inserting an already-present id adds another heat factor.
- Roots are the union of the three marked supports. Connectivity to
  that union alone is not three-mark connectivity; the proved separate
  mark-cut filter is retained. Supports may overlap or overapproximate.
- Three agents worked independently on factorization, reusable finite
  resummation, and the local normalization proof. The parent supplied the
  integrated original-response statements and ran all compiler checks
  serially. A subsequent read-only review checked roots, endpoint factors,
  repeated insertion, the extra insertion exponent and size dependence.
- Next analytic input: a useful spatial bound on the remaining rooted
  coefficients or signed sum, retaining the actual normalization cost
  and any necessary cancellations. This increment supplies no such decay.
- All-nome temporal composition on one stationary physical carrier,
  required volume/spacing control, continuum QFT/nontriviality, physical
  mass normalization and the all-compact-simple-group target remain open.
  No ordinary heat-bath/L2 estimate is identified with physical OS time.

## 4. Verification boundary

Four new modules passed focused checks through `scripts/safe_lean_build.py`
with one worker and the mandatory 20 GiB ceiling. All 22 public axiom gates
are subsets of {propext, Quot.sound}; some definitions are axiom-free.
Eight serialized launches included two namespace corrections, the integrated
term-bound recheck, and the final documentation-precision recheck. No new
hole, custom axiom, classical input or weakened canonical field was added.

Direct dependency artifacts were newer than their sources; no dependency
rebuild or raised limit was needed. Four root imports were added.
Root/full-tree compilation and a full axiom audit were NOT run.
Final local log hashes:

- `/tmp/BF4ExactSlabResponseSpectatorFactorization.log`:
  `b04f9eb9b8d77c93e790634b7f41e8df75f626c4f02dffc52f9d9c0f9002e2a0`.
- `/tmp/BF4ExactSlabRootedFunctionalResummation.log`:
  `5104245b6f1f8c541bf898be05f648245c2d30fe5ed26ff5b2bcdcea3a2244ea`.
- `/tmp/BF4ExactSlabResponseCollarNormalization.log`:
  `d78b11db6b2bb060d5d35fc6c31fa625807c908b88af7808733c140322e2e9f2`.
- `/tmp/BF4ExactSlabRootedResponseResummation.log`:
  `47def47f0de5f1f6a784bbf27d6daefc3e402add697e6b805229b56cee735957`.

CI remains manual-only. The whole-project goal remains active.
