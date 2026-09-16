# Actual physical-time covariance and strict centered form bound

Date: 2026-09-16. PROGRESS after `e70f3b0`.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills on R^4,
required QFT axioms and a positive physical Hamiltonian gap for EVERY compact
simple group, on the SAME theory, within the constructive axiom gate. The
result below concerns the selected original fixed-spatial SU(2) action, not
the continuum or all-group target.

## Checked mathematical argument

1. Fix physical signed presentations x,y and an explicit common radius R.
   In chart H=R+n, the lower advanced-y offsets are R-d; the upper reflected-x
   offsets are H+d. The mixed insertion is therefore the original lower
   source polynomial times the H-slice lift of the original upper source.
   The two windows have lengths R and H, gap n, and total length 2H.
   The chart, finite action, cutoff and partition are identical in the
   joint term and both unit marginals. The order of the two marginal factors
   is explicitly commuted before using the previous covariance theorem.
2. Arbitrary common shifts require PADDED coefficient equality. Empty
   schedules retain the unit with padded zero exponents. Before using the
   padded finite-ratio congruence, both source and target insertions are
   proved supported on the full (2H+1)-slice carrier. No variables outside
   that carrier are silently dropped.
3. Polynomial caps depend only on coefficients and signed face words, not
   their time labels. The resulting presentation prefactor is the explicit
   separationCap(width,x,y)=4*cap(sourceSpan x)*cap(sourceSpan y).
   The SAME finite connected scalar satisfies |covariance|<=A*q^n at every
   boundary depth t; n and t are independent. The existing connectedLimit
   retains this bound on its own actual approximations, each a finite scalar
   at its constructed QMhat index. No limit interchange is needed.
4. The computed centeredMoment is the intrinsic lag-n pairing minus the
   two unshifted unit coefficients. Its RC class equals the SAME completed
   centered-time pairing, and thus the SAME connectedLimit. This proves the
   physical-time envelope, without choosing an RC representative.
5. For v=center(embed x), let m(k)=B(v,T_(2k)v). Actual time balance gives
   m(k)=B(T_k v,T_k v)>=0; constant-one contraction gives m(k)<=m(0).
   Actual completed Cauchy--Schwarz gives m(k)^2<=m(k+k)*m(0).
   The proved envelope gives m(k)<=(1+A)*(q*q)^k, with positive computed
   prefactor 1+A. The generic constructive dyadic theorem removes that
   prefactor: m(1)<=q*q*m(0). Its positive-rate hypothesis is used only when
   q>0. The complementary rational branch has q equivalent to zero and uses
   the lag-two envelope directly, without dividing by a norm or rate.
6. For a supplied physical Cauchy stream X, the actual mixed-pairing limits
   and scalar product continuity construct the limit of the centered moments
   of X.seq(k). The already prefactor-free dense bound passes through those
   limits. No uniform coefficient cap for X.seq(k) is required, and pointwise
   centering is not identified with the separately regularized center stream.
   Proposition-valued quotient induction extends the bound to every completed
   centered vector, without selecting a representative. The actual even-time
   diagonal identity gives the one-step squared-norm bound. Both estimates
   restrict to the existing UnitComplement via center_fixed_iff.

Thus, on this actual completed unit complement,
`B(v,T_2 v) <= q*q*B(v,v)` and
`B(T_1 v,T_1 v) <= q*q*B(v,v)`, with `q*q < 1`.

Expansion exposes the chart, supported lifts, original partition and
moment identities. Contraction composes the finite estimate, its actual
scalar limit and dyadic inequalities into a norm-relative form bound.
No new analytic input, axiom, sorry or weakened frontier field is used.

## Declaration evidence

All paths have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `mirrorSpan_encodeChart` | `BF4ExactSlabFixedSpatialReflectedSeparatedProbe.lean:62` | Guarded exact reflected-distance geometry. |
| `windowProbe_advance`, `sourceSpan_advance` | `BF4ExactSlabFixedSpatialReflectedSeparatedProbe.lean:92`, `:108` | Whole-polynomial padded lifts, including empty schedules. |
| `mixedProduct_reflected_separated` | `BF4ExactSlabFixedSpatialReflectedSeparatedProbe.lean:128` | Actual reflected insertion becomes the separated product. |
| `separationCap`, `separationCap_nonnegative` | `BF4ExactSlabFixedSpatialPhysicalCovariance.lean:65`, `:69` | Computed lag-independent presentation envelope. |
| `chart_joint_separated`, `chart_upper_marginal`, `chart_lower_marginal` | `BF4ExactSlabFixedSpatialPhysicalCovariance.lean:110`, `:132`, `:155` | Three original finite pins at the SAME chart/action/partition. |
| `connectedScalar_abs_le`, `connectedLimit_bounds`, `centeredMoment_le` | `BF4ExactSlabFixedSpatialPhysicalCovariance.lean:175`, `:209`, `:231` | Physical-lag finite decay and actual connected scalar-limit envelope. |
| `centeredMoment`, `centeredMoment_pin` | `BF4ExactSlabFixedSpatialCenteredMoments.lean:46`, `:52` | Explicit representative of the actual centered form. |
| `evenMoment`, `evenMoment_diagonal_pin` | `BF4ExactSlabFixedSpatialCenteredMoments.lean:61`, `:71` | Even-moment index k means physical lag 2*k. |
| `evenMoment_nonnegative`, `evenMoment_le_zero`, `evenMoment_dyadic` | `BF4ExactSlabFixedSpatialCenteredMoments.lean:86`, `:94`, `:102` | Actual moment hypotheses, not an assumed moment package. |
| `twoStepRate`, `twoStepRate_nonnegative`, `twoStepRate_lt_one` | `BF4ExactSlabFixedSpatialDenseCenteredGap.lean:45`, `:48`, `:53` | Computed q*q in [0,1), independent of retained stage. |
| `evenMoment_le_geometric`, `evenMoment_first_le`, `dense_twoStep_form_gap` | `BF4ExactSlabFixedSpatialDenseCenteredGap.lean:78`, `:97`, `:138` | Prefactor removal and actual centered dense norm-relative estimate. |
| `representativeCenteredMoment`, `representativeCenteredMoment_converges`, `representativeCenteredMoment_pin` | `BF4ExactSlabFixedSpatialCompletedCenteredGap.lean:51`, `:61`, `:77` | Actual supplied-stream limits and same-completed-carrier pin. |
| `representative_twoStep_form_gap`, `completed_twoStep_form_gap` | `BF4ExactSlabFixedSpatialCompletedCenteredGap.lean:87`, `:99` | Dense inequality passes to supplied streams and their quotient. |
| `completed_oneStep_norm_gap` | `BF4ExactSlabFixedSpatialCompletedCenteredGap.lean:112` | Strict squared-norm contraction from actual even-time diagonal identity. |
| `unitComplement_twoStep_form_gap`, `unitComplement_oneStep_norm_gap` | `BF4ExactSlabFixedSpatialCompletedCenteredGap.lean:122`, `:130` | Both estimates on the actual unit-orthogonal subtype. |

Only the model-independent scalar declaration
`Z4HalfTimeReflectionStrictJointDenseDyadicGap.lean:365`,
`dyadic_geometric_first_le`, is reused from that older path. Its old-model
specializations do not identify or supply any of the actual current objects.

## Parameters and honest boundary

The original physical-time map is geometric advance of observables, NOT
a link heat-bath dynamics. Positivity is proved for its even subsemigroup;
this does not assert one-step positive semidefiniteness.

For every fixed nome 0<w<1 and width, q=mixRate(w,width) is in [0,1).
The envelope and q*q do not depend on retained heat stage. The constructed
state/carrier still has fixed cutoff: a common rate is not itself a joint
cutoff/time limit theorem. No width/spacing-uniform rate, physical-unit
mass calibration or continuum Hamiltonian has been constructed here.
The result includes q=0, zero norm and degenerate zero-width presentations.

Nonconstant excitations, full required observable algebra and Hilbert/OS
reconstruction, metric completeness, joint cutoff/time limits, spatial and
spacing passage, continuum QFT and all compact simple groups remain open.
Do not infer a nonzero excitation or continuum mass from a strict form
inequality on a potentially trivial unit complement.

## Focused verification

The five modules above passed focused serialized one-worker/20 GiB checks,
each with fresh process/swap preflight. All 35 public gates depend only on
{propext, Quot.sound}. Final logs have no warnings, errors, sorryAx or
classical dependencies. Namespace-resolution errors in the first physical
covariance check were repaired without changing statements or resource
settings. Main alone compiled; parallel work used disjoint files/read-only
reviews. No root/full-tree/full axiom audit or literature scan was run.
Five imports were added to the selective root without claiming a root check.

| Module suffix (prefix BF4ExactSlabFixedSpatial) | Gates | Final `/tmp/<module>.log` SHA-256 |
|---|---:|---|
| `ReflectedSeparatedProbe` | 4 | `52efdbf97af24fe883adb0c861bed7960db147c5c3cc10530712e85771b06e7b` |
| `CenteredMoments` | 9 | `19ef52cb3ac2e1c14c7b47cbf4a954c438c31e66ec7880d278a5b2b8361e81a5` |
| `PhysicalCovariance` | 8 | `1972abede74d68d4e46bb211d0168b4409037fd0a3493c9fe93d7b2faf9e180a` |
| `DenseCenteredGap` | 6 | `8e5b728fae997ca8785d667bbdd0b5bf877f9fd7baf0e4465cd2c3971cf80209` |
| `CompletedCenteredGap` | 8 | `895b38155b7a11c2c2876dce1d83a7612608d24a2e7128c3f6cb234dcdf24cef` |

## Next causal frontier: fixed-width cutoff/time passage

This paragraph records source review, not a new theorem. For a fixed common
chart H and fixed physical probes, write S(k,t)=chartScalar(width,k,H,x,y,t).
`BF4ExactSlabFixedSpatialCommonChartCorrelator.lean:102`, `chartCauchy`, and
`:122`, `chartCauchy_modulus`, supply a boundary-time modulus independent of
cutoff k. At fixed t, `chartScalar` at `:61` is literally the original
`finiteValue` with fixed extent, chain and insertion;
`BF4ExactSlabAllNomeFaceSetExpectation.lean:65`, `finiteCauchy`, supplies its
cutoff modulus. The three-hop comparison through one chosen boundary depth
already exists for a different, one-sided scalar as
`BF4ExactSlabFixedSpatialOriginalJointCauchy.lean:89`,
`originalJoint_rectangle`. Its reflected common-chart instantiation is the
next missing consumer. Do not infer a cutoff-independent connected modulus
from generic multiplication: construct the three chart limits first, then
combine their diagonal streams with the existing scalar Cauchy arithmetic.

The spatial obstruction is separate and explicit:
`BF4ExactSlabFixedSpatialTransferSandwich.lean:57`, `kineticFloor`, is
headFloor(w)^F, and `:61`, `kineticCap`, is prefixCap(w)^F, where F is the
number of temporal faces. `BF4ExactSlabFixedSpatialTransferMixingRate.lean:81`,
`mixFraction`, is floor/cap, and `:110`, `mixRate`, is 1-floor/cap.
No width-uniform positive floor for that fraction or spacing-dependent
physical mass calibration is supplied by the present proof.
