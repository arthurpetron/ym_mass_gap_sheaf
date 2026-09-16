# Positive original central variance and same-carrier completed pairing

Date: 2026-09-16. PROGRESS after `9cb7613`.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills on R^4,
the required QFT axioms and a positive physical Hamiltonian gap for EVERY
compact simple group, on the SAME theory and within the constructive
axiom gate. This checkpoint concerns SU(2), fixed nome and positive fixed
spatial width. It does not close the continuum or physical-gap target.

## Mathematical increment

Let u_t = T^t 1, ell(f) = H[V*f], M_t = ell(u_t), and S be the number
of spatial faces. The original central density is exactly

    W_t = V * u_(t+1)^2.

The existing transfer floor/cap a,b certify a*M_t <= u_(t+1) <= b*M_t
in the actual polynomial square-certificate cone. Product certificates,
with shared variables retained, give

    L*M_t^2 <= W_t <= U*M_t^2,
    L = headFloor(w)^S * a^2,
    U = prefixCap(w)^S * b^2,
    delta = L/U > 0.

EXPANSION retains one central spatial potential and both actual messages.
CONTRACTION cancels their common boundary-mass square without comparing
unrelated normalized measures: H[W_t] <= U*M_t^2 implies
delta*H[W_t] <= L*M_t^2. Adding the explicit nonnegative constant difference
to the lower certificate gives a certificate for W_t-delta*H[W_t].

Inserting any supported square and dividing by the SAME positive mass
therefore gives E_W[r^2] >= delta*H[r^2]. The generic variance comparison
tests r = p-E_W[p], with that center computed explicitly. Thus
Var_W(p) >= delta*Var_H(p); no minimization oracle is used.

The concrete p is the fundamental character of the actual origin p01
spatial plaquette. Its source-slice Haar mean is zero and square moment is
one. These are transported from the original physical-face character
identities by the actual slice embedding, not substituted from a model
character law. Width > 0 ensures this face is present. The radius-zero
physical presentation has exact first/second-moment pins to the original
central ratio, with the SAME chart, action, cutoff and partition.

Consequently its finite original variance is at least delta for every
late cutoff and every positive boundary depth. Evaluate at stage k+1 and
depth k+1, so both moments lie on the same shifted joint diagonal. Scalar
limit continuity then proves the cutoff-removed centered reflected
moment at time zero is at least ofQ'(delta).

Independently, actual limiting CS gives quantitative mixed-pairing
continuity. Supplied Cauchy streams provide explicit anchor norm ceilings;
the computed closed outer rate and actual inner regularity epsilon.den
construct their mixed scalar limit. Explicit closeness rates descend it
to the EXISTING JointCompletion, without representative selection or a
fixed-stage carrier identification. The completed pairing is symmetric,
positive on diagonals, normalized on the unit, and equals jointPairing on
embedded presentations. Hence the positive variance is also the positive
Gram determinant of the embedded character and unit on that SAME carrier.

## Declaration evidence

Paths in this table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Checked content |
|---|---|---|
| `spatialFloorCertificate` | `BF4ExactSlabFixedSpatialWeightedMass.lean:92` | Existing proof made public; proof body unchanged. |
| `centralDensity`, `centralDensity_lower`, `centralDensity_upper` | `BF4ExactSlabFixedSpatialCentralDensity.lean:88`, `:123`, `:140` | Actual density and common-mass-square certificate bounds. |
| `centralFraction`, `centralFraction_positive`, `centralDensity_normalizedFloor` | `BF4ExactSlabFixedSpatialCentralDensityFloor.lean:90`, `:93`, `:119` | Explicit positive delta and original normalized-density floor. |
| `normalized_square_floor`, `normalized_variance_comparison`, `normalized_variance_floor` | `QuaternionHaarDensityVariance.lean:101`, `:221`, `:237` | Generic certificate-to-square/variance comparison at the computed mean. |
| `character_mean_zero`, `character_square_one`, `span` | `BF4ExactSlabFixedSpatialCentralCharacter.lean:112`, `:132`, `:154` | Concrete original character, Haar moments and physical presentation. |
| `chartScalar_mean_pin`, `chartScalar_square_pin` | `BF4ExactSlabFixedSpatialCentralCharacter.lean:201`, `:215` | SAME original central first/second moments. |
| `normalizedMoment_middleRatio`, `centralVariance_floor`, `chart_variance_floor` | `BF4ExactSlabFixedSpatialCentralVariance.lean:57`, `:79`, `:92` | Actual normalized-density and original-chart variance lower bound. |
| `normBase`, `normCeiling`, `diagonal_le_normCeiling` | `BF4ExactSlabFixedSpatialJointPairingBounds.lean:41`, `:43`, `:80` | Explicit Cauchy-anchor bounds. |
| `pairing_close` | `BF4ExactSlabFixedSpatialJointPairingContinuity.lean:81` | Quantitative joint squared-distance continuity. |
| `rawRate`, `pairRate`, `representativeInner`, `representativeInnerCauchy` | `BF4ExactSlabFixedSpatialJointPairingLimit.lean:49`, `:78`, `:96`, `:108` | Actual explicit-rate scalar completion. |
| `completedInner`, `completedInner_embedSpan`, `completedUnit_norm_one` | `BF4ExactSlabFixedSpatialJointCompletedInner.lean:91`, `:112`, `:142` | SAME-carrier descent, original pin and normalization. |
| `central_joint_variance_floor`, `central_completed_gram_pin`, `central_completed_gram_floor` | `BF4ExactSlabFixedSpatialJointCentralVariance.lean:92`, `:109`, `:118` | Strict positive lower bound in the joint reflected form and completed Gram determinant. |

## Parameter dependence and remaining consumer

Delta depends on nome w and spatial width. The theorem quantifies over
every K >= headCutoff(w) and every t+1 boundary depth at those fixed
parameters. No spatial-width, coupling-window or lattice-spacing uniform
floor is asserted. The generic variance argument is group-agnostic;
its SU(2) density/character instance does not imply a continuum U(1) gap.

The next short consumer is the actual centered completed vector. Use
the explicit rational presentations x-mu.approx(n)*unit, where
mu = jointPairing(x,unit), with its existing QCauchy data. Prove this stream
Cauchy in the joint distance, its unit pairing zero, and its self-pairing
equal to the positive determinant. This is a source-reviewed next argument,
not a vector already constructed here; it does not require first building
all completed real-scalar operations.

General completed linearity/centering and the strict completed gap extension,
positive definiteness/metric completeness/full Hilbert and OS/QFT structure,
spatial/spacing control, physical mass calibration, continuum nontriviality
and all-group Clay closure remain open. No canonical field, analytic premise,
literal hole or axiom changed. A nonconstant lattice observable is not a
non-Wick continuum theory or a positive physical Hamiltonian gap.

## Verification boundary

Eleven focused serialized one-worker/20 GiB file checks passed: 80 public
gates in ten new modules and eight gates in the existing WeightedMass module.
Every reported dependency is within {propext, Quot.sound}. Final logs contain
no warnings, errors, sorryAx or classical dependencies. Main alone compiled;
parallel work used disjoint files and read-only source review.

The initially missing canonical-pairing-completion object was supplied by
one monitored dependency-complete `+Module:olean` target. Its quiet log is
empty; axiom evidence comes from the focused downstream logs, not that log.
Singleton/limit elaboration timeouts were resolved by generic coefficient
lemmas, explicit scalar sequences and named chart equivalences; no heartbeat
or resource limit was raised. Ten selective-root imports were added.
Root/full-tree/full axiom audit were NOT run. No literature scan ran.

Final log files below are under `/tmp/`:

| Log | Gates | SHA-256 |
|---|---:|---|
| `ym-central-weighted-mass.log` | 8 | `8fa1ac270efa7ccae188717c5262de4c513e82db93fe8c7d4d7be09e5d0cbcef` |
| `ym-central-density.log` | 11 | `5d71d8b603f6e4d5872d63ef9d0f5c1ac338c4c58726d4dbd00022517408e85d` |
| `ym-central-density-floor.log` | 8 | `2ad5927af5f3d886ff313352dfd97179d8c4b0f381fcf09e5525d64534cd5707` |
| `ym-central-character.log` | 13 | `45e72642d90333dd5236a8c6cb18561e918003c3db4b7348c238bd446031e78b` |
| `ym-haar-density-variance.log` | 5 | `89fbdf4fa83ca054bbe362ce5c1c9f2db14c04b792e7eda6aeb7dc210f576ad7` |
| `ym-central-variance.log` | 3 | `c7df010611bbaabd70bc63632eac4b1c127234e57eae4405196fca409c3eebf1` |
| `ym-joint-pairing-bounds.log` | 6 | `da95cbbce3d3a4015d7009214c839cd0f37d92d0425048f3f5d6558d515852a2` |
| `ym-joint-pairing-continuity.log` | 3 | `5be79cc12eb52dba939ee718f302d7ad50cf2b42f46cf5a454b0dd172594e2fd` |
| `ym-joint-pairing-limit.log` | 13 | `26319fe1bb2f1850c0ecdf23f78f617e0907f2ff56a651c0b71fc8970d0bc497` |
| `ym-joint-completed-inner.log` | 12 | `7854f47ccb4457f84a05ecef000d9d15da73dfbabbc8abb6066a58a4963dc06d` |
| `ym-joint-central-variance.log` | 6 | `af30c5a5c45464226ba654602c270bcbb9be549f8d6ae4ec437bf8a489ca3e29` |
