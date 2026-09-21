# Actual local heat-defect bound on the same signed polynomial

Date: 2026-09-21 UTC. WHOLE-PROJECT GOAL remains OPEN: constructive,
nontrivial continuum Yang--Mills on R^4 for every compact simple group,
with the same theory's full QFT axioms, isolated vacuum and finite positive
physical mass gap. This is a finite SU(2) local kinetic estimate.

## New mathematical result

Let H be the original product quaternion-Haar functional, and let P_K be
the actual one-link conditional heat operator. For every supported signed
polynomial p and rational 0<=w<1, the new theorem proves

    H[p^2] - H[p * P_K p] <= (1-w) * H[angularSquare p]

whenever K is at least the computed `sufficientCutoff w`. There is NO
restriction requiring the degree of p to be below K. Every signed cross
term in p is retained. The bound is on the original polynomial's complete
six-plane angular energy, not an assumed comparison norm.

Independently of that large-cutoff guard, for 0<=w<=1 the original local
quadratic form lies between zero and H[p^2] at every finite cutoff. These
claims use the genuine nonnegative harmonic multipliers; they do not assume
pointwise positivity of the truncated heat polynomial.

## Exact identity of the operator and carrier

On an enlarged carrier (x,y,z), `copy p` is p(x,z): it inserts a zero
exponent quaternion block immediately after the head and retains ALL tail
exponents. `liftHead q` is q(y,z). Thus the local pairing is literally

    H_(tail+2)[relativeHeat(w,K;x,y) * p(x,z) * q(y,z)].

The spectators z are shared, not integrated separately for p and q.
The output map is computed by the EXISTING `conditionalHeat` applied to
`copy p`. Its support, normalized mean, and pairing with every test q
are pinned to this original integral.

Three exact joins remove the preceding checkpoint's missing assumptions:

1. `copy_derivative` and `copy_laplacian` preserve the head differential
   operations on padded representatives. `copy_carrier` is proved through
   the existing lift and an explicit block swap, with both support guards.
2. `substitute_copy_prefix` proves that retained substitution of the copy
   is the original p on (y,z), coordinate by coordinate. Carrier equality
   then uses the proved supports; raw padding is not silently erased.
3. `polynomial_diagonal` applies original heat reproduction to the computed
   complete harmonic groups and uses unequal-degree orthogonality. It proves

       H[p * P_K p] = sum_d a_K(d) H[h_d^2].

   The norm identity gives the corresponding defect sum. The already proved
   all-degree cutoff/Casimir bound controls it. Finally
   `polynomial_angular_energy` reconstructs H[angularSquare p] from the
   complete groups, using angular integration by parts, the exact Casimir,
   and carrier transport. No decomposition or diagonalization is a premise.

## Source map

All paths in this table are under `lean/YMGap/Continuum/`.

| Declaration | Source | Result |
| --- | --- | --- |
| `copy` | `SU2QuaternionSpareHeadCopy.lean:52` | Explicit p(x,z) on the enlarged (x,y,z) carrier. |
| `copy_derivative` / `copy_laplacian` | `SU2QuaternionSpareHeadCopy.lean:114` / `:143` | Head calculus preserved with explicit padding. |
| `substitute_copy_prefix` | `SU2QuaternionSpareHeadCopy.lean:232` | Same p(y,z) after actual retained substitution. |
| `copy_carrier` | `SU2QuaternionSpareHeadCopy.lean:282` | Arbitrary-insertion carrier embedding with both support guards. |
| `polynomial_angular_energy` | `SU2QuaternionGroupedAngularEnergy.lean:260` | Original total angular energy, including same-degree cross terms. |
| `harmonic_pair` | `SU2QuaternionHeadHeatDiagonal.lean:56` | Original kernel multiplier on a genuinely copied harmonic. |
| `polynomial_pair` / `polynomial_diagonal` | `SU2QuaternionHeadHeatDiagonal.lean:100` / `:157` | Arbitrary original input, actual local kernel, computed groups. |
| `polynomial_defect` | `SU2QuaternionHeadHeatDiagonal.lean:195` | Actual local defect equals complete-group attenuation defect. |
| `polynomial_pair_nonnegative` / `polynomial_defect_nonnegative` | `SU2QuaternionHeadHeatDiagonal.lean:212` / `:221` | Local quadratic form between zero and the original norm. |
| `headMap` | `SU2QuaternionHeadHeatDiagonal.lean:247` | Existing conditional heat with the constructed copy. |
| `headMap_supported` / `headMap_mean` / `headMap_pairing` | `SU2QuaternionHeadHeatDiagonal.lean:250` / `:256` / `:264` | Same carrier, normalized mean and actual original pairing. |
| `headMap_defect_le_angular` | `SU2QuaternionHeadHeatDiagonal.lean:271` | Finite-time defect bounded by original angular energy. |

## The next product join is not yet proved

`headMap` is NOT singleton `productMap`. The latter Haar-averages all
unselected lower slots. The former preserves unselected coordinates as
shared spectators. In particular, substituting one for the other would
change the operator.

The next necessary edge is composition of correctly selected conditional
local updates into the actual product kinetic map, with the remaining
inactive Haar projections explicit, or an equivalent exact hybrid
telescope. Current consumers are:

- `SU2QuaternionProductHeatMarginals.productMap_pairing`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:247`;
- `SU2QuaternionProductHeatHarmonicExpansion.productMap_selected_expansion`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatHarmonicExpansion.lean:158`;
- `BF4ExactSlabFixedSpatialActiveEnergy.energy_active`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:129`.

The selected-factor expansion retains the remaining factors; it does not
identify that remaining expression with the local diagonal norm. The
existing `productMap_square_split` concerns conditional Haar projection
and fluctuation, not the required composition of local heat updates.

Even after a product-kinetic comparison, the signed endpoint correction in
`BF4ExactSlabFixedSpatialGroundStateEnergy.energy_eq_bare_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`,
must be retained. The differential cancellation is not automatically the
finite-time weighted comparison. SAME-variance relative control, spatial
and scaling survival, finite physical mass, full QFT and all groups remain
open. A local ordinary-Haar kinetic estimate is not an OS/Hamiltonian gap.

## Verification boundary

Sol supplied angular-energy reassembly and independently reviewed the
coordinate bookkeeping and actual-product distinction. Main supplied the
explicit copy, original local kernel diagonalization, quantitative consumer,
and integration. No canonical field, analytic premise, hole or axiom was
introduced, removed or weakened.
Sol's final read-only review of the completed bound, local-map pins and
this report passed, including the cutoff quantifiers and source citations.

Focused check logs:

- `/tmp/ym-gap-spare-head-copy-check.log`
- `/tmp/ym-gap-grouped-angular-energy-check.log`
- `/tmp/ym-gap-head-heat-diagonal-check.log`

All three focused checks passed, with 28 printed gates confined to
`{propext, Quot.sound}` and no warnings, errors, `sorryAx`, classical axioms
or native-decider dependencies. The dependency-complete consumer target
below passed as well. The root import list is updated; the full root was
not checked in this increment.

The dependency-complete consumer is
`+YMGap.Continuum.SU2QuaternionHeadHeatDiagonal:olean`, with log
`/tmp/ym-gap-head-heat-diagonal-build.log`. Checks use ONE capped 20 GiB
worker with the existing OS-reserve and pressure safeguards. No full-root
build, full axiom audit or frontier guard is claimed.
