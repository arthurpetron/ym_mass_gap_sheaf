# Actual cutoff-limit Haar transfer and rank-one cone bounds

Date: 2026-09-16. Classification: PROGRESS after `1b7c0fc`.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4,
the required QFT axioms and a positive physical Hamiltonian gap for every
compact simple group, on the SAME theory, within the constructive axiom gate.
The ordinary-Haar operator constructed here is not yet the physical OS operator.

## Actual operator, not just a Cauchy estimate

For rational 0<w<1 and fixed spatial width, `completedLimit` is a map on the
existing ordinary-Haar GNS completion. It is constructed from the actual
finite-cutoff transfer maps; neither action weights nor T are rescaled.
Write C=stepCap(w,width). For every completed x,y it satisfies

    ||T_limit x||^2 <= C^2 ||x||^2,
    ||T_limit x-T_limit y||^2 <= C^2 ||x-y||^2,
    ||T_limit x-T_K x||^2 <= epsilon^2 ||x||^2

where the last inequality holds for epsilon>0 and
K>=transferCutoff(w,width,epsilon). The threshold is independent of x,
NOT independent of w or width. The SAME map is additive and rational homogeneous.

The representative construction uses lateCutoff(w,p)=max(headCutoff(w),p).
For a supplied Cauchy representative X, its existing eventual norm ceiling
computes familyDelta=invSucc(max(epsilon.den,normCeil X)); its square times
the norm ceiling is bounded by epsilon. Thus the actual cutoff family has
an explicit outer modulus. The existing constructive diagonal supplies
limitRep, with representative modulus gMod. No quotient representative is
chosen, and no witness is extracted from a propositional existence claim.

Null descent fixes ONE common outer cutoff before comparing inner indices.
The norm/distance bounds pass to the diagonal through joint pairing continuity.
For the final cutoff estimate K remains fixed; only the outer family index
is shifted to max(p,transferCutoff). This retains the original epsilon^2
constant with no loss. Linearity uses exact original polynomial identities
at one common cutoff followed by three-hop quadratic comparisons.

Paths in the tables have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Checked content |
|---|---|---|
| `familyDelta`, `familyDelta_budget` | `BF4ExactSlabFixedSpatialTransferLimitFamily.lean:49`, `:58` | Computed norm-dependent tolerance and its rational budget. |
| `cutoffFamily` | `BF4ExactSlabFixedSpatialTransferLimitFamily.lean:103` | Actual maps and an explicit outer Cauchy modulus. |
| `limitRep`, `limitRep_modulus` | `BF4ExactSlabFixedSpatialTransferLimitFamily.lean:132`, `:136` | Computed diagonal with its existing explicit modulus. |
| `familyRate`, `family_close_at` | `BF4ExactSlabFixedSpatialTransferLimitFamily.lean:141`, `:155` | Computed outer rate and eventual inner-index comparison. |
| `limitRep_null`, `completedLimit` | `BF4ExactSlabFixedSpatialCompletedTransferLimit.lean:38`, `:63` | Null descent and actual map on the existing quotient. |
| `completedLimit_norm_bound`, `completedLimit_distance_bound` | `BF4ExactSlabFixedSpatialCompletedTransferLimit.lean:76`, `:94` | Original cap on every completed input/pair. |
| `completedLimit_cutoff_bound` | `BF4ExactSlabFixedSpatialCompletedTransferLimit.lean:134` | Norm-relative estimate against the constructed limit, at the original input-independent threshold. |
| `completedLimit_add`, `completedLimit_smul` | `BF4ExactSlabFixedSpatialCompletedTransferLimitLinear.lean:136`, `:146` | Addition and rational scaling for this actual limit map. |

## Original-kernel rank-one sandwich

For supported certified f and K>=headCutoff(w), define

    a = headFloor(w)^length(temporalFaces(width)),
    b = prefixCap(w)^length(temporalFaces(width)),
    ell_K(f) = H_N[V_K*f].

The new constructors return polynomial Haar-cone certificates for
T_K f-cap(a*ell_K(f)) and cap(b*ell_K(f))-T_K f. These are stronger than
bare inequalities of total integrals: subsequent certificate operations can
consume them on the retained spatial carrier.

The kinetic lower certificate uses the elementary product identity
(u-c)*v+c*(v-c^m)=u*v-c^(m+1), with both positive factors certified. It
requires no coordinate independence. Both sides then multiply by the same
supported V_K*f, enlarge its certificate with the proved support guard,
and integrate the actual N head blocks. A head-only supported polynomial
integrates to its exact Haar constant. Precisely one V_K is retained.

| Declaration | Module:line | Checked content |
|---|---|---|
| `kineticFloor`, `kineticCap`, `weightedMass` | `BF4ExactSlabFixedSpatialTransferSandwich.lean:57`, `:61`, `:65` | Explicit constants and original V_K-weighted functional. |
| `kineticFloor_positive` | `BF4ExactSlabFixedSpatialTransferSandwich.lean:68` | a>0 for 0<w<1. |
| `kineticFloorCertificate` | `BF4ExactSlabFixedSpatialTransferSandwich.lean:108` | Certificate for the complete kinetic product minus its floor. |
| `partialHaarHeads_supported_constant` | `BF4ExactSlabFixedSpatialTransferSandwich.lean:173` | Coefficientwise head-only Haar constant, not just equality of total integrals. |
| `weightedMass_nonnegative` | `BF4ExactSlabFixedSpatialTransferSandwich.lean:191` | Nonnegative ell_K for certified f. |
| `transferStepLowerCertificate`, `transferStepUpperCertificate` | `BF4ExactSlabFixedSpatialTransferSandwich.lean:197`, `:223` | Actual rank-one lower and upper certificate constructors. |

a and b are independent of the late heat cutoff, but ell_K still depends on
K through V_K. Nonnegative ell_K does not justify division for arbitrary f.
The comparison is in the finite polynomial cone, not a proved closed cone
on the limiting completion. Cone preservation is not operator positive
semidefiniteness. No strict contraction is asserted here.

## Remaining causal consumers and boundaries

The single-step cutoff-limit construction is now supplied. Compatibility of
its finite powers/pairings with the original scalar cutoff limit still needs
proof; the terminal V_K*g also changes with cutoff and must be retained.
Quantitative comparison of positive original messages is the next consumer
of the sandwich, with explicit positive normalization witnesses required.
There is no new ratio-contraction declaration in this checkpoint.

Stationary vacuum, physical reflected OS realization, width/spacing-uniform
control, continuum QFT/nontriviality and all compact simple groups remain
open. No canonical frontier field or old theorem statement is weakened.

## Verification boundary

Four focused serialized checks passed all 35 public axiom gates within
{propext, Quot.sound}, using one worker and the 20 GiB ceiling. A family
binder was renamed to avoid a local notation collision; the sandwich retry
added two missing namespace opens. No literal hole, new axiom, analytic
premise or normalization was introduced. Independent source reviews found
no mathematical mismatch in the same-object limit or the sandwich.
Four selective-root imports added; root/full-tree verification and the full
axiom audit were not run. CI remains manual-only.

| Focused log in `/tmp/` | SHA-256 |
|---|---|
| `BF4ExactSlabFixedSpatialTransferLimitFamily.log` | `530ddce59c6dfc26779447008f79af4229b9054f58c2e69f99544342ffa54b29` |
| `BF4ExactSlabFixedSpatialCompletedTransferLimit.log` | `bcb684753f9a437bae4d79504e953336143ba8b9f39f0e0ae6a6883c85acf040` |
| `BF4ExactSlabFixedSpatialCompletedTransferLimitLinear.log` | `da281c3adbb66155adc1065dd64c8a146a16c80d47f7d13e205df35d9dc2e709` |
| `BF4ExactSlabFixedSpatialTransferSandwich.log` | `759694dbf6cf15c565b4c529e824a40cea8aaefb6976e60b298aa8257c269b1b` |
