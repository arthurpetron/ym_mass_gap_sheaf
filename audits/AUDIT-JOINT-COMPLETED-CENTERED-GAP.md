# Actual joint unit complement, nonzero excitation and strict form bound

Date: 2026-09-16. PROGRESS after `54346f5`.

WHOLE-PROJECT GOAL: nontrivial continuum quantum Yang--Mills on R^4,
the required QFT axioms and a positive physical Hamiltonian gap for EVERY
compact simple group, within the constructive axiom gate and on the SAME
theory. This checkpoint proves fixed-nome, fixed-spatial-width SU(2)
statements, not a continuum or Hamiltonian-gap theorem.

## Mathematical contraction

For an original physical presentation x, let mu = J(x,unit). The actual
stream x-mu.approx(k)*unit has squared distance between terms m,n exactly
(mu.approx(m)-mu.approx(n))^2. Its explicit modulus is
`meanCauchy.M (min epsilon 1)`: the clipped scalar tolerance controls the
square without a square root or a selected real-scalar action.

That stream constructs a vector c(x) in the EXISTING JointCompletion.
Scalar limit uniqueness proves

    B(c(x),unit) = 0,
    B(c(x),T_n c(y)) = jointCenteredMoment(n,x,y).

All symbols denote the already pinned original pairing, unit and literal
physical time. The limit does not replace the state, action or partition.
Changing rational centering coefficients occurs after the original joint
cutoff/time limits, not inside an unjustified fixed-observable limit.

The universal completed estimate has an even shorter route. For ANY supplied
joint Cauchy representative X, its centered scalar moments converge to
the completed time pairing minus the product of its two unit coefficients.
The prefactor-free dense two-step bound passes through these three scalar
limits. Quotient induction descends it; orthogonality removes the correction.
Consequently, for every completed v with B(v,unit)=0,

    0 <= B(v,T_2 v) <= twoStepRate(w,width)*B(v,v),
    0 <= twoStepRate(w,width) < 1.

No uniform coefficient-presentation cap is required. Completed time balance
preserves this actual unit complement, gives its discrete semigroup, and
identifies B(T_1 v,T_1 v) with B(v,T_2 v). The two-step map is positive in
this form sense; positivity of one-step time is NOT asserted.

For positive width, c(original origin plaquette character) is an actual
element of this sector. Its norm equals the previously proved joint
variance and is at least the explicit positive centralFraction(w,width).
Thus it is distinct from the embedded zero, not merely a formal Gram
determinant or a nonzero constant unit. Its norm representative has explicit
QCauchy data, and its physical-time correlator has the exact original pin.

## Declaration evidence

Paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `centerApprox`, `physicalTime_centerApprox` | `BF4ExactSlabFixedSpatialJointCenterAlgebra.lean:39`, `:43` | Actual rational centering and literal time compatibility. |
| `centerApprox_pairing`, `centerApprox_distance` | `BF4ExactSlabFixedSpatialJointCenterAlgebra.lean:139`, `:176` | Exact mixed form and coefficient-change squared distance. |
| `centeredRate`, `centeredStream`, `centeredVector` | `BF4ExactSlabFixedSpatialJointCenteredStream.lean:74`, `:77`, `:88` | Computed modulus and actual vector on the existing carrier. |
| `centeredVector_orthogonal`, `centeredVector_time_pairing` | `BF4ExactSlabFixedSpatialJointCenteredPairing.lean:93`, `:132` | Zero unit pairing and original connected-moment realization. |
| `representativeCenteredMomentCauchy`, `representativeCenteredMoment_converges` | `BF4ExactSlabFixedSpatialJointCompletedGap.lean:55`, `:70` | Explicit scalar data and same-representative limit. |
| `completed_twoStep_form_gap`, `completed_even_nonnegative` | `BF4ExactSlabFixedSpatialJointCompletedGap.lean:150`, `:160` | Universal actual completed unit-complement inequalities. |
| `completedInner_time_balance`, `UnitComplement`, `unitComplementTime` | `BF4ExactSlabFixedSpatialJointUnitComplement.lean:54`, `:71`, `:74` | Same-pairing balance and invariant sector. |
| `twoStepTransfer`, `unitComplement_oneStep_norm_gap` | `BF4ExactSlabFixedSpatialJointUnitComplement.lean:92`, `:111` | Restricted even-time transfer and one-step squared-norm bound. |
| `centralExcitation`, `excitationNormCauchy` | `BF4ExactSlabFixedSpatialJointCentralExcitation.lean:46`, `:52` | Witnessing orthogonal vector and norm modulus. |
| `centralExcitation_norm_floor`, `centralExcitation_ne_zero`, `centralExcitation_correlator_pin` | `BF4ExactSlabFixedSpatialJointCentralExcitation.lean:67`, `:74`, `:90` | Explicit positive norm, nonzero proof and same-object correlations. |
| `twoStepRate`, `twoStepRate_nonnegative`, `twoStepRate_lt_one` | `BF4ExactSlabFixedSpatialDenseCenteredGap.lean:45`, `:48`, `:53` | Existing actual q-squared rate, including q=0. |

## Next analytic frontier, not another required centering interface

The comparison is uniform over completed vectors at FIXED nome and width.
It is not width-, coupling-window- or spacing-uniform. The definitions
`kineticFloor` and `kineticCap` in
`BF4ExactSlabFixedSpatialTransferSandwich.lean:57` and `:61` are per-face
floor/cap powers; `mixFraction` in
`BF4ExactSlabFixedSpatialTransferMixingRate.lean:81` divides those quantities.
The source-level algebra therefore gives, with r=headFloor/prefixCap and
T the temporal-face count, q=1-r^T. The central floor similarly contains
r^(S+2T), by `densityFloor` and `densityCeiling` in
`BF4ExactSlabFixedSpatialCentralDensity.lean:78` and `:81`, and
`centralFraction` in `BF4ExactSlabFixedSpatialCentralDensityFloor.lean:90`.
These products are a volume-loss
warning, not proof that the ACTUAL gap or variance degenerates. This
checkpoint adds no kernel-checked width-asymptotic theorem.

Bulk geometry is a separate obstruction. `spatialFaces_mem_iff` and
`temporalFaces_mem_iff` in
`BF4ExactSlabFixedSpatialFacePlacement.lean:98` and `:104` use spatial bases
0 <= x_i < width. `BF4ExactSlabFixedSpatialCentralCharacter.face` at
`BF4ExactSlabFixedSpatialCentralCharacter.lean:74` is the origin plaquette.
Increasing width alone leaves it beside three lower spatial boundaries.
Time-boundary forgetting is not spatial-boundary forgetting.

NEXT: construct explicit recentered embeddings of fixed local probes in
larger original spatial boxes, and prove same-action comparison with a
spatial-boundary modulus. Seek a connected even-time envelope for those
probes with rate rho(w)<1 independent of width. Its prefactor MAY depend
on width and presentation: the existing
`Z4HalfTimeReflectionStrictJointDenseDyadicGap.dyadic_geometric_first_le`
at `Z4HalfTimeReflectionStrictJointDenseDyadicGap.lean:365` removes a positive
prefactor using positivity, contraction and dyadic moment inequalities.
The rate-zero case must be handled separately, as on the current dense path.
This is an OPEN analytic target and an existing consumer, not an assumed
estimate or a new frontier bundle. Do not demand a uniform prefactor merely
to feed that consumer. The older
`BF4ExactSlabThermodynamicCovarianceRate.covariance_geometric_bound` at
`BF4ExactSlabThermodynamicCovarianceRate.lean:119` concerns its different,
fixed-small-nome full-slab objects; no identification is asserted here.

Completed general linear/centering laws, positive definiteness and metric
completeness/full Hilbert structure, the full original observable/gauge
algebra and OS/QFT reconstruction still require their own proofs. Spatial
and spacing passage, physical time/mass calibration, continuum nontriviality
and all-group Clay closure remain open. No canonical field has been closed
or weakened by this checkpoint. A strict form bound is not by itself a
constructed continuum Hamiltonian or a spectral identification theorem.

## Verification boundary

Six focused module checks passed all 58 public gates, each within
{propext, Quot.sound}. Final logs contain no errors, warnings, sorryAx or
classical dependencies. Main alone compiled with one worker and the 20 GiB
cap, after fresh process/swap preflights. Parallel work was disjoint source
construction and read-only mathematical review. Independent review found no
same-object, normalization, positive-width or operator-scope defect.

An initial pairing check exposed an over-opaque local mean definition;
removing that local irreducibility marker fixed the definitional comparison.
No proof hypothesis, resource limit, sorry or axiom was added. Six root
imports were added; root/full-tree/full axiom audit were NOT run. No
literature scan ran. Final logs below are in `/tmp/`:

| Log | Gates | SHA-256 |
|---|---:|---|
| `ym-joint-center-algebra.log` | 8 | `b0fdc5acd9bb042c6c5baa52f7350da31eab402c8566734e06b2ed62922abf4f` |
| `ym-joint-centered-stream.log` | 11 | `9869824877446f3a4c71ffa6bf9da4da58ffb867968b7c17701f5c97c285ecbf` |
| `ym-joint-centered-pairing.log` | 6 | `50fda82e931200e3c834bef7ca1a65dbb3274313430893cc84708b0c12fc427e` |
| `ym-joint-completed-gap.log` | 11 | `08ab0b10f0b261d0e162d518ba9e02bd159a8ce9121140e7b8c073bacca7aa37` |
| `ym-joint-unit-complement.log` | 13 | `ce4a7523c13b15d87e90cf9c8bf2d7cae2d913c181fbde7c3c7f9c1835f9a02a` |
| `ym-joint-central-excitation.log` | 9 | `5349f9410efe4a65659044d1f5f860447c9ca5bf5a1453dbfe3d68a4147ffee6` |
