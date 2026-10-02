# Original signed-margin degree and finite exponent universe

## Outcome and actual consumer

PROGRESS after `8ad6f62`: the actual finite-cutoff terminal message has block
degree <=K at EVERY depth. The complete original central edge and its joint
family projection have degree <=8*K in each original endpoint block,
independently of spatial width, depth and nome. ALL six literal margin
insertions have degree <=2, including both means and the whole signed jump.
Their compressed numerators belong to one COMPUTED finite exponent list
depending only on K and the supplied family length.

This removes the degree-growth obstacle left by the previous footprint
reduction. It does not bound coefficient size, raw term multiplicity,
construction cost or runtime, and supplies no accepted useful signed margin.

The actual recipient is `FamilyJointDensity.compressedPairing`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointDensity.lean:211`),
whose original insertion pin is `compressedPairing_pin` (same file, line 217).
`finite_margin_pin` (same file, line 362) joins those original evaluations to
`BF4WilsonAllNomeFiniteReferenceMargin.check`
(`lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:267`).
That checker still requires ACTUAL accepted finite positive-margin data.

## Mathematical argument

1. The literal original kinetic product is a product over DISTINCT active
   link pairs. A character of spin n has block degree <=n; its retained heat
   prefix therefore has degree <=K in either paired link. Off-pair factors
   have degree zero. Hence the WHOLE kinetic product has degree <=K per block.
2. A literal spatial plaquette has degree one in an incident link and omits
   nonincident links. Direct induction over the ORIGINAL ordered face list
   charges K only at incident factors. The existing geometric count is <=6.
   No coefficient-equivalence or quotient-degree shortcut is used.
3. At each original transfer step, the spatial weight and input occupy only
   the integrated lower slice. They have degree zero in the retained upper
   blocks. Integrating the heads and shifting the survivors preserves their
   degree ceiling. Thus terminal iteration resets degree to K, independently
   of its input degree and depth.
4. Each endpoint of the ORIGINAL edge pays kinetic K, spatial <=6*K and
   terminal <=K. The opposite endpoint factor is independent. Joint spectator
   projection cannot increase degree; compression reads the SAME exponents.
5. The complete signed spatial family is a SUM of degree-one characters,
   even with repetitions, overlaps and negative coefficients. Lower/upper
   means have degree <=1; second/mixed moments and the COMPLETE squared jump
   have degree <=2. No cross term is dropped.
6. The smaller embedding has <=8*qs.length blocks. Its supported raw exponent
   lists have degree <=8*K+2 per block. The existing constructive bounded-
   monomial enumeration places them in
   `monomials (8*qs.length) (fun _ => 8*K+2)`. Extra enumerated blocks have
   literal zero exponents. This is a finite list, not a claimed independent
   basis or a bound on repeated terms.

## Checked declarations

| Declaration | Source | Exact scope |
| --- | --- | --- |
| `kineticWeight_lower_degree` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticDegree.lean:187` | Whole original lower-block degree <=K. |
| `kineticWeight_upper_degree` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticDegree.lean:196` | Whole original upper-block degree <=K. |
| `spatialWeight_degree` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDegree.lean:259` | Whole original spatial degree <=6*K, all source slots. |
| `step_degree_reset` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointDegree.lean:87` | Retained ceiling comes from the kernel, not input degree. |
| `terminalMessage_degree` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointDegree.lean:109` | Actual original terminal degree <=K, all depths. |
| `density_degree` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointDegree.lean:164` | Complete joint projection <=8*K per block. |
| `marginInsertions` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointDegree.lean:268` | Partition, BOTH means, second/mixed moments, whole squared jump. |
| `marginInsertions_degree` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointDegree.lean:275` | All six actual signed insertions <=2 per block. |
| `marginMonomials` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointDegree.lean:293` | Computed finite list from cutoff and face count only. |
| `margin_numerators_monomials` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointDegree.lean:314` | EVERY compressed numerator term belongs to that SAME list. |

## Parameters and scope

The new degree assertions quantify over arbitrary rational nome w, cutoff K,
width and terminal depth. The degree ceilings depend on K, not on w, width
or depth; the enumerated list also depends on family length. Actual polynomial
coefficients retain their nome, width and depth dependence. Membership
of each supplied face in the ORIGINAL spatial face set is explicit where
needed for the signed insertion bound. No sign or nonempty-family premise is
added. The existing positive normalized evaluations still use 0<w<1 and
K>=headCutoff(w); their action, partition, OWN means and cutoff moduli are
unchanged. These are SU(2) quaternion-polynomial statements, not an every-group
construction or a beta-uniform mass-gap assertion.

## Verification boundary

All commands ran serially through `scripts/safe_lean_build.py` with `--jobs 1`,
`--check-worker-limit-gib 20`, the explicit changed `--check` file and matching
`--check-output` under `lean/.lake/build/lib/lean/YMGap/Continuum/`.

| Checked module | Accepted log | Result |
| --- | --- | --- |
| `BF4ExactSlabFixedSpatialKineticDegree` | `/tmp/ym-kinetic-degree-20261002-check.log` | Exit 0, five public gates. |
| `BF4ExactSlabFixedSpatialSpatialDegree` | `/tmp/ym-spatial-degree-20261002-final.log` | Exit 0, four public gates. |
| `BF4ExactSlabFixedSpatialFamilyJointDegree` | `/tmp/ym-family-joint-degree-20261002-final.log` | Exit 0, twenty public gates. |

All 29 gates are within {propext,Quot.sound}; `marginMonomials` is axiom-free.
No error, warning or sorryAx occurs in the accepted logs. Earlier failed
draft logs are NOT evidence. No sorry, new axiom, classical/native oracle,
analytic premise, witness erasure or weakened frontier was introduced.
Sol independently reviewed the original-object mathematics: PASS.
Luna independently checked source/log hashes, declaration lines, all 29 gates,
documentation scope and byte-identical canonical chart fences: PASS.

Pre/post live memory checks reported 86%/85% memory-pressure free and zero
swap; no compiler or runner survived. ONE 20-GiB worker and the 12-GiB reserve
were unchanged. One root import added. Full root/tree build, axiom audit,
guard and progress-metric script NOT run. CI and exact canonical chart claims
remain unchanged; no ASCII reprint.

| Artifact | SHA-256 |
| --- | --- |
| `BF4ExactSlabFixedSpatialKineticDegree.lean` | `da6df465484a5ed5ac7e1f5f320591f9f93402daca93bf436fc5d0e1bf603538` |
| `BF4ExactSlabFixedSpatialSpatialDegree.lean` | `3419b3d31c2dec40adeb444f06794a8d021e7ae3050fe106db515099abcc5caa` |
| `BF4ExactSlabFixedSpatialFamilyJointDegree.lean` | `653f74821729d5c6e4324ebaba24cc5dd651c4fcee72d15d06307703e49a6d7d` |
| `/tmp/ym-kinetic-degree-20261002-check.log` | `82907763958ba93fed6121cf7cedae9fe3092973264f8979cdecbe57aedcc1e9` |
| `/tmp/ym-spatial-degree-20261002-final.log` | `59222f136fc69dba44e2fc5bd020d15f4f58c030adf4b225bdad0a1036f6ab70` |
| `/tmp/ym-family-joint-degree-20261002-final.log` | `df5fd442e481a787e0097451b23ad7b57cbd23b0299b0b3dd3cbb50311afd4ee` |

## Repointed frontier

NEXT: control or evaluate the actual ORIGINAL coefficients/moments in this
fixed-cutoff finite exponent universe, preserving shared partition factors
and signed cancellations, to produce a useful accepted margin on a justified
changing family. Degree grows with cutoff; no all-cutoff finite list is claimed.
Raw multiplicity, coefficient size, full projection cost and feasible runtime
remain unbounded. The universe may be large and is not a practical algorithm
by itself. Physical spacing/lower gap, nonzero continuum survival, full SAME-
theory QFT, every-group realization and the Clay theorem all remain OPEN.
