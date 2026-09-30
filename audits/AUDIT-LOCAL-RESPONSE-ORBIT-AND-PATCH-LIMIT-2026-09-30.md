# Original physical-time survival and face-patch covariance limit

Date: 2026-09-30 UTC. Whole-project Clay target remains OPEN.
Verification status: all four final focused checks passed; see the exact
verification boundary below.

## The mathematical step back

The preceding source-orbit audit rules out a seed-only Dirichlet floor as a
uniform **upper-decay** producer. A different implication is valid for a
**lower-response** floor on the positive original physical-time operator.
Write r_n = <x,T^n x> and y = Tx-rho*x. Positivity gives

    0 <= <y,T^n y> = r_(n+2)-2*rho*r_(n+1)+rho^2*r_n.
    e_(n+1) >= rho*e_n, where e_n = r_(n+1)-rho*r_n.
    rho >= 0 and e_0 >= 0 imply r_n >= rho^n*r_0.

This is an elementary weighted second-difference induction. It uses no
division by a vector norm, spectral theorem, or classical choice. It does
NOT reverse the earlier obstruction: lower survival is not upper decay.

## Supplied original plaquette inputs

`BF4WilsonAllNomeResponseLower.response_geometric_lower`
(`lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:117`) propagates the
lag-one floor on the actual all-nome Wilson completion. Positivity of every
time power comes from `BF4WilsonAllNomeTimeDefectMoments.mixedMoment_nonnegative`,
not from an assumed spectral representation.

`BF4WilsonAllNomeLocalResponseOrbit.plaquette_local_response_floor`
(`lean/YMGap/Continuum/BF4WilsonAllNomeLocalResponseOrbit.lean:97`) joins the
existing scalar original connected response to the LITERAL Wilson plaquette
using its actual mean and lag pins. There is no identification between
differently named completions. The input c(w) is the constructed
`BF4ExactSlabFixedSpatialLocalResponse.localResponseFloor`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalResponse.lean:69`), namely

    c(w) = headFloor(w)^56 / ((w^(-12)+5)*prefixCap(w)^56).

This displayed formula describes the rational value; the code uses positive
rational reciprocals, explicit positivity witnesses and localLower/localUpper.
The existing squared-norm cap four gives rho(w)=c(w)/4. The existing positive
norm floor s(w)=starRatio(w) then supplies

    s(w)*rho(w)^n <= <v,T^n v>,
    s(w)*rho(w)^(2*n) <= ||T^n v||^2,
    T^n v != 0.

These conclusions are `plaquette_response_absolute_lower` at
`lean/YMGap/Continuum/BF4WilsonAllNomeLocalResponseOrbit.lean:134`,
`plaquette_time_norm_floor` at line 144 and `plaquette_time_ne_zero` at line
151 of the same file. The strict-padding theorem is
`padded_plaquette_response_absolute_lower` at line 166.

The hypotheses are rational 0<w<1, a spatial face and its four active links.
Strict padding supplies activity for a face in each strictly larger width.
Both s and rho are independent of width, heat cutoff and terminal depth,
but DEPEND ON w. Each width retains its own existing carrier. Every n is a
finite integer physical lattice-time lag; no fixed-physical-time scaling
lower bound, width-limit vector, completed width embedding or full-carrier
time injectivity follows. Inactive fringe states have not been removed.

## Supplied face-patch covariance input

`BF4ExactSlabSmallNomeChebyshevCovarianceLimit.covariance_sq_bound_of_finite`
(`lean/YMGap/Continuum/BF4ExactSlabSmallNomeChebyshevCovarianceLimit.lean:41`)
passes a single stage-independent finite squared-covariance factor through
the existing three scalar cutoff limits. The old public small-nome theorem
and its hypotheses are preserved.

`BF4ExactSlabFacePatchCovarianceLimit.finite_patch_covariance_sq_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFacePatchCovarianceLimit.lean:126`)
supplies the finite consumer's reverse-energy input from the ACTUAL coupled
auxiliary in `BF4ExactSlabFacePatchUniformCoercivity.coupled_auxiliary_reverse_energy`.
The centered coefficient is (1-36*e(w))/2 and the parameter is
c=2+(2/625)*(1-36*e(w))/2. There is no new assumed successful source budget.

`patch_covariance_sq_geometric_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFacePatchCovarianceLimit.lean:183`) gives

    Cov(p,q)^2 <= r(w)^(2*n)*Var(p)*Var(q), r(w)=1/(c-1), 0<r(w)<1,

for the original cutoff-removed finite-slab law and its OWN diagonal
variances. The guards remain explicit: 0<w<1, heatRatio<=1/2,
heatRemainderBound<1, positive face-patch margin, supported local p/q,
and disjointness of testSupport from grow(extent,16*n,support).
The rate has no extent or cutoff argument. The support-separation guard
does not permit n to grow arbitrarily at one fixed extent with fixed p,q.

`expandedNome_patch_covariance_sq_geometric_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFacePatchCovarianceLimit.lean:207`) discharges the nome
guards at the exact nome 1/40, where the preceding old margin was negative.
This is spatial covariance decay at fixed coupling. The auxiliary balanced
conditional sweep B=W*W is NOT identified with physical OS time T.

### Downstream consumer check

No direct spatial-limit consumer of this new full-slab bound was found in
the following inspected modules:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformConnectedDecay.lean:135`,
  `connectedScalar_selected_pin`, pins the original connected scalar to a
  covariance with `chartIds`, not the full `slabPhysicalFaceEdges` action.
  `connectedScalar_uniform_bound` in the same file uses that selected action.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:90`,
  `spatialCenteredMoment_bound`, consumes the selected-chart decay bound and
  `originalConnected_diagonal_converges`, not the new full-slab estimate.
- `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCenteredCompletion.lean:224`,
  `centeredPairing_geometric_bound`, uses its existing `covariance_geometric_bound`
  to approximate an already constructed pairing; it is not a generic spatial
  Cauchy consumer of the new squared bound.

Thus no spatial-limit closure is asserted. An action-preserving new estimate
or a proved quantitative comparison would be needed to use that route; no
finite equality between the full and selected actions is assumed here.

## Remaining causal frontier

These are two supplied-input joins, not additional budget interfaces. They
do not construct the changing-coupling signed source estimate, same-object
spatial/scaling comparison, continuum nontriviality, physical Hamiltonian,
finite positive physical mass, full QFT axioms or every compact simple group.
No canonical chart field changes. The next primary task remains an estimate
on the actual original source orbit, or an original signed multiscale defect
at matched physical time, with a quantitative scaling budget.

## Verification

Four final focused checks exited zero. Every printed gate reports only
`[propext, Quot.sound]`:

| Module under `lean/YMGap/Continuum/` | Printed gates | Final local log |
| --- | ---: | --- |
| `BF4ExactSlabSmallNomeChebyshevCovarianceLimit.lean` | 6 | `/tmp/ym-covariance-limit-20260930.log` |
| `BF4WilsonAllNomeResponseLower.lean` | 3 | `/tmp/ym-response-lower-20260930.log` |
| `BF4WilsonAllNomeLocalResponseOrbit.lean` | 10 | `/tmp/ym-local-response-orbit-20260930.log` |
| `BF4ExactSlabFacePatchCovarianceLimit.lean` | 14 | `/tmp/ym-face-patch-covariance-limit-20260930.log` |

Each used `scripts/safe_lean_build.py --jobs 1 --status-seconds 300
--check-worker-limit-gib 20 --check <file> --check-output <matching olean>`.
Checks were serialized, with the launcher's dynamic memory/pressure guard
and 12 GiB OS reserve intact. Earlier draft elaboration failures were repaired;
only the successful final checks support this report.

No new sorry, custom axiom, unsupplied analytic premise or weakened frontier
field; no old sorry discharged. Root imports were added. No full-root/tree
build, full audit, guard or CI run was performed. Independent read-only
reviews checked the weighted-positivity argument, original-action covariance
quantifiers, and the absent direct spatial-limit consumer.
