# Inverse-free local dual route for the original signed family

Date: 2026-09-30 UTC. Whole-project Clay target OPEN.
Classification: PROGRESS. Polynomial factorization, same-weight double
adjoint pairing and mixed-derivative annihilation are kernel-checked.

Priority correction, later on 2026-09-30: the finite fixed-nome signed-family
floor was already proved in `BF4ExactSlabPlaquetteAffineCoercivity`; this
route is not needed to establish its existence. Physical cube instantiation
is suspended absent a demonstrated coupling-cost improvement. The literal
Wilson completion join is now proved separately; see
`AUDIT-WILSON-SIGNED-FAMILY-JOIN-2026-09-30.md`. The proved identities below
remain valid. The numbered next obligations record the superseded plan.

## Why take this further step back?

The checked two-Ward upper estimate controls each coefficient detector,
but summing separate per-face estimates costs the number of faces. A family
argument needs control of the full Gram matrix of its tests. Locality of
arbitrary observables is not enough: the interacting measure can correlate
distant observables. Derivative-adjoint duals have an additional exact
integration-by-parts identity that arbitrary observables do not have.

## Polynomial construction, with no reciprocal

For selected angular derivatives X at link a and Y at link b, split the
original action W=V*A, where A is the product of faces incident to either
link and X(V)=Y(V)=0. Define the polynomial

    J = 6*(X A)*(Y A)*g + 3*A*(Y X A)*g
        + 3*A*(X A)*(Y g) + 3*A*(Y A)*(X g) + A^2*(Y X g).

Its factorization is A*J=Y X(A^3*g). In particular, the notation
"A inverse times Y X(A cubed times g)" is NOT its definition: there is
no division, reciprocal choice or reciprocal convergence in the construction.
Two integrations by parts give

    H[W*J*f] = H[W*A^2*g*(X Y f)].

The order reverses under the two adjoints; no commutation premise is needed
for these identities. The original background and the additional A^2 factor
are retained exactly. If X Y f is zero, the left pairing is zero despite the
interacting weight. This is a statement about a derivative dual, not a
general clustering or independence claim.

## Concrete original-action consumer still to supply

Choose a,b to be the two physical edges already used in coefficient
isolation and g=X Y f_p. The existing source isolation then provides
X Y(F-m)=c_p*g. The proposed detector pairs as

    H[W*J*(F-m)] = c_p*H[W*A^2*g^2].

Sum all 36 direction pairs. The checked physical mixed-square floor supplies
the kinematic factor eight; the local product floor must still be inserted
twice to bound this new detector's diagonal.

Relevant existing declarations for the physical instantiation:

- `BF4ExactSlabLocalSupportComparison.fullWeight_split`,
  `lean/YMGap/Continuum/BF4ExactSlabLocalSupportComparison.lean:79`, splits
  the actual full action with its detached background retained.
- `BF4ExactSlabBlockNormalizer.collarHeat`,
  `lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:61`, is the local A.
  `background_independent` at :92 supplies independence from selected links.
- `BF4ExactSlabLocalSupportComparison.collarCount_le`,
  `lean/YMGap/Continuum/BF4ExactSlabLocalSupportComparison.lean:56`, bounds
  the two-link collar by at most twelve faces, independently of extent.
- `BF4ExactSlabRetainedHeatHeadComparison.headProduct_weighted_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:186`,
  inserts a local product into any certified positive background.
- `BF4ExactSlabPlaquetteMixedSquare.physical_face_weighted_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabPlaquetteMixedSquare.lean:113`,
  is the actual physical 36-direction kinematic floor.

These declarations are prerequisites, not a claim that the physical
collar-dual consumer or family theorem is already composed.

## Next obligations and limits

1. Instantiate the polynomial dual on the actual two-link collar and prove
   its local support and coefficient pairing, on the unchanged action.
2. Prove exact far-collar Gram annihilation using the double-IBP identity,
   then give the finite collar-overlap count. Do not replace this by assumed
   mixing or infer orthogonality merely from disjoint observable supports.
3. Construct an explicit local norm cap UNIFORM IN HEAT CUTOFF. A fixed-K
   syntactic polynomial cap is insufficient. Heat factors need mixed
   first/second derivative bounds; the finite face test also needs its
   explicit higher derivative caps. The generic mixed heat interval producer
   is `QuaternionHaarHeatSecondAngularDerivative.heatPrefixSecondAngularIntervalAt`,
   `lean/YMGap/Continuum/QuaternionHaarHeatSecondAngularDerivative.lean:102`.
4. Compose a signed-family Cauchy--Schwarz/Gram bound, then realize it on the
   SAME literal completed carrier. None of these four obligations is closed
   by the local polynomial identities alone.

This route pays a local heat-floor cost. If ell is the local product floor,
d the verified row-count bound and C_J the verified dual norm cap, the planned
normalized coercivity has a cost of the form 64*ell^4/(d*C_J^2). Those inputs
and the final inequality are not yet supplied as a physical family theorem.
No polynomial control as the nome approaches one is asserted. Width/cutoff
control at fixed nome would still not be scaling survival, every-state decay,
physical mass calibration, continuum QFT or the every-group Clay theorem.

## Verification boundary

New declarations:

- `QuaternionHaarRetainedDoubleIBP.retained_pair`, `retained_double_pair`
  and `retained_double_annihilates`,
  `lean/YMGap/Continuum/QuaternionHaarRetainedDoubleIBP.lean:35`, :61, :77.
- `QuaternionHaarLocalCubeAdjoint.cubeAdjoint` and `cubeAdjoint_factor`,
  `lean/YMGap/Continuum/QuaternionHaarLocalCubeAdjoint.lean:60`, :184.
- `QuaternionHaarLocalCubeDual.local_cube_dual_pair` and
  `local_cube_dual_annihilates`,
  `lean/YMGap/Continuum/QuaternionHaarLocalCubeDual.lean:35`, :75.

All three files passed focused serialized monitored checks, seven public
gates in {propext, Quot.sound}, at default heartbeat limits. Final logs:
`/tmp/ym-retained-double-ibp-20260930.log`,
`/tmp/ym-local-cube-adjoint-20260930.log`,
`/tmp/ym-local-cube-dual-20260930.log`. One worker, 20 GiB hard worker cap,
12 GiB OS reserve and dynamic safety telemetry. No new sorry, axiom,
classical premise, analytic hypothesis bundle, or changed frontier field.
No full build/audit/guard, raised memory limit, Rust computation or CI change.
Sol supplied the finite cube factorization and reviewed the local-dual
argument; root supplied the double-IBP/weighted composition and all checks.
The canonical chart has not changed and is not reprinted.
