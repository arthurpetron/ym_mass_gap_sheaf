# Original Haar quartic certificate: forward/backward meeting

Date: 2026-10-02 UTC. The actual original polynomial certificate and its
positive-source consumer are checked. Signed centered-source control,
OWN interacting variance comparison and the continuum/Clay goal remain OPEN.

## Backward producer: computed degree and actual square witness

`rowCutoff`, `normalizedRow_error`, `unnormalizedRow_reconstruction` and
`unnormalizedRow_nonnegative`, respectively
`lean/YMGap/Continuum/BernsteinRationalPositiveRow.lean:119`, line 187,
line 83 and line 264, operate on the actual rational coefficient list p.
For a supplied PROVED strict margin eta>0 on [0,1], the degree is computed
from p and eta. The coefficient error is <=eta/2 at EVERY later degree;
the actual unnormalized row is nonnegative and reconstructs p exactly
at ALL rational arguments. No row, reconstruction or modulus is assumed.

`strictPolynomialCertificate`,
`lean/YMGap/Continuum/QuaternionHaarBernsteinRowCertificate.lean:205`,
constructs the Type-valued `Certificate blocks (subst y p)` from that
margin and actual certificates for y and 1-y. Exact row reconstruction
is reflected through the existing finite polynomial root-count theorem
and coefficient-level substitution, not multivariate evaluation inference.
The square terms retain shared variables and support arbitrary permitted
Haar insertions. `unitArgument_certificate`, `oneMinusUnitArgument_certificate`
and `unitArgument_unshift`,
`lean/YMGap/Continuum/QuaternionHaarUnitIntervalCoordinate.lean:52`,
line 65 and line 87, construct y=(1+X)/2 from an actual unit square bound
and pin 2*y-1 to X at coefficient level.

## Forward producer: the ORIGINAL polynomial and unchanged consumer

`eta_le_unitMargin_eval` and `subst_classMarginPolynomial`,
`lean/YMGap/Continuum/SU2HeatJacobiFinitePrefixClassPolynomial.lean:152`
and line 234, give the strict margin and exact original polynomial pin.
Both original heat prefixes use SAME inclusive K and K+1 labels.
`quarticMarginCertificate`,
`lean/YMGap/Continuum/SU2HeatJacobiOriginalHaarQuarticBound.lean:49`,
composes these producers into the ACTUAL original Haar square witness.
Its hypotheses are the original nome bounds, positive rational margin,
both original spacing-cutoff guards and an actual unit scalar square bound;
it does not assume the target Haar certificate or a heat profile.

`selectedChordInsertion_le_original` at line 91 invokes
`affine_original_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialHeatNomeComparison.lean:135`.
The selected insertion is literally [2(1-X)]^2*heatPrefix(q,K,X), against
the SAME positive endpoint source, spectator action, width, depth and odd
partition. The relative scalar uses length(baseLinks(width))+i and i on
the existing doubled SAME-width carrier. No heat-floor reciprocal occurs.

## Computed all-later tolerance cutoff

Write c(q)=40*24576^2*(1-q)^2. `quarticCutoff`, `cutoff_guards` and
`quarticPrefixError_budget`, respectively
`lean/YMGap/Continuum/SU2HeatJacobiOriginalHaarQuarticCutoff.lean:59`,
line 74 and line 101, combine the original head cutoff and BOTH original
tail tolerance cutoffs. The explicit allocations are eta=epsilon/2,
T_q<=epsilon/64 and T_(q*q)<=epsilon/[4*(1+c(q))]. Thus
16*T_q+c(q)*T_(q*q)+eta<=epsilon. There is no reciprocal of c(q).

`selectedChordInsertion_le_tolerance` at line 140 proves, for
16/17<=q<1, epsilon>0, every width/depth/active i and EVERY K at least
quarticCutoff(q,epsilon),

    original selected quartic insertion <= (c(q)+epsilon)*original oddMass.

The existing `oddMass_positive`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:69`,
constructs the partition positivity used to enlarge the coefficient;
no partition-positivity hypothesis is added.

## Boundary and next causal obligation

This closes the pointwise-to-original-Haar-certificate join for the positive
source consumer. It is NOT a bound for a signed centered bilateral source,
the complete signed cost, OWN interacting variance or a scaling response.
Those joins still require proofs. Useful spatial/spacing control, a justified
scaling family, nontrivial continuum survival, physical mass calibration,
full SAME-theory OS/QFT and every compact simple group remain OPEN.
No exact displayed canonical chart claim changes.

## Verification

All six final focused monitored checks passed: 49 public axiom gates,
each within {propext,Quot.sound}. One worker, explicit 20-GiB hard ceiling,
12-GiB OS reserve and fresh dynamic preflights were used; pressure-free
memory was 84--85 percent with zero swap. Final logs have no errors,
warnings, sorryAx, Classical.choice or unsafe decision axioms.
Rejected local elaboration attempts were repaired; the new width notation
was corrected to the existing consumer's argument-binding notation before
accepting its bounds. No existing Lean declarations were changed.

| Artifact | SHA256 |
| --- | --- |
| Rational row source | `1bd3061d747a49390c913bd77692ce2ef0cff737fdf95f965d394f59c1d5c050` |
| Haar row source | `a47ab80237bd3dac1e9632c57fb8be92dc45fd7a03ca252209082e6ccff891d2` |
| Unit coordinate source | `69a84afd1951b8c18a88fea4e8c8c1c06e6a81349ca2e09ff1b3d42b2dae1f72` |
| Class polynomial source | `c9cb86d594731e10cd0e085851e1a4aae2f042053532ba92ff47dd9b370af04c` |
| Original bound source | `d7e6027c119c1fe932524a4a00a3f5d7369f5bddeb20b8969ca524f312619c94` |
| Cutoff source | `609d8d0102d5f6e4f87a721d2ba8babd0fa04e24c7aae501060e1698b52beae9` |
| `/tmp/ym-bernstein-positive-rational-row-20261002-first.log` | `c3eee4e24abe69248b7a6f6738ecea70c05cb5ff82e2bc8bf8961dbed27349f2` |
| `/tmp/ym-haar-bernstein-polynomial-20261002-second.log` | `f15e3e8cac1e534551e60c8630b0b90c8b0592da940940a16c9441142024be78` |
| `/tmp/ym-haar-unit-coordinate-20261002-second.log` | `b5ba64717cdcb0e8726125aceb6ae450c59db17ddf206113fbba5c0baf99ef8d` |
| `/tmp/ym-jacobi-class-polynomial-20261002-third.log` | `e90efa62434974b9d65f059de4f1c919dc247740e9d87b792ef2e469e26080b8` |
| `/tmp/ym-jacobi-original-haar-quartic-20261002-second.log` | `5f9d2f7445b685ef448a64a2a45e50c7bf09ff42608967a8bf634d73c1c058f2` |
| `/tmp/ym-jacobi-original-haar-quartic-cutoff-20261002-first.log` | `b5a1a9bf82c04b274b248ff19007dadda62b8dee23f48f64878a0becc261a6ee` |

Six root imports are registered, not aggregate-checked. No broad root/tree,
guard or audit was run. No new sorry, axiom, classical shortcut, weakened
field, surrogate source, resource ceiling or CI change was introduced.
The canonical chart fence is unchanged and is not reprinted.
