# Original width-one fringe source — 2026-09-17 UTC

## Whole-project goal and scope

Construct a nontrivial continuum quantum Yang--Mills theory on R^4 for every
compact simple gauge group, with the required SAME-theory QFT structure,
isolated vacuum and finite positive physical mass gap, within the repository's
constructive Lean axiom gate. This increment is an original-action SU(2)
producer diagnostic, not a physical gap or continuum theorem.

The current probe is an individual quaternion scalar and is NOT gauge-invariant.
It tests the existing producer on arbitrary supported polynomials. Conclusions
about it cannot refute a gauge-invariant-only replacement, a different producer,
or the Clay target. In particular, the desired constant may depend on the nome;
the whole-project goal does not require one constant for every bare coupling.

## The literal objects

`baseLinks_length`, `activeBlocks_one` and `early_fringe`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOneGeometry.lean:36`, `:67`, `:109`,
give 24 original coordinates, active blocks [0,1,4], and early fringe block 2.
`spatialFaces_one` and `activeSpatialFaces_one` in the same file (`:57`, `:75`)
identify the three origin spatial faces and the empty fully-active face list.
No coordinates are removed from the original marginal.

In the literal numeric order the three quaternion face words are

    p01 = q0*q3*bar(q2)*bar(q1),
    p02 = q0*q6*bar(q5)*bar(q4),
    p12 = q1*q8*bar(q7)*bar(q4).

`face01_pin`, `face02_pin`, `face12_pin` and `spatialWeight_pin`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOnePacketMoment.lean:242`, `:252`,
`:262`, `:273`, pin these words and ALL THREE original heat prefixes.
Their shared active links are not independent plaquette variables.

Define f=q4.scalar and

    X = q3*bar(q2)*q8*bar(q7)*q5*bar(q6),
    chi = 2*scalar(X),       r = chi*f,       r_shift = (chi-2)*f.

These are `hexQuaternion`, `hex`, `probe`, `insertion` and `bareProduct`,
`lean/YMGap/Continuum/SU2QuaternionCornerFundamentalMoment.lean:56`, `:58`,
`:59`, `:60`, `:61`; `tester`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOnePacketMoment.lean:96`; and
`shiftedTester`, `lean/YMGap/Continuum/BF4ExactSlabWidthOneFringeMoment.lean:49`.

The marginal remains nu=V*g0*g1, with V the original three-face weight and
g1 the actual original terminal. `terminal_one` and `marginal_haar`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOneSource.lean:121`, `:140`, prove
g1 is one and nu is V under every supported Haar test. These are NOT free
polynomial coefficient identities. Removing V as well is permitted only
for the separately proved fringe-independent insertions.

`mass_one`, `probe_mean_zero`, `probe_norm` and `centered_probe`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOneSource.lean:160`, `:165`, `:168`,
`:174`, give mass one, mean zero, squared norm 1/4, and partition-cleared
Phi=f. `source_haar` at `:180` pins the actual source nu*Phi to V*f under
supported tests, without substituting a product-density analogy.

## The exact moment and original-source join

`selected_product_zero` and `any_slot_product_zero`,
`lean/YMGap/Continuum/SU2QuaternionOrientedWordSelection.lean:153`, `:204`,
extend oriented character selection with an arbitrary supported spectator.
The scalar character can be cycled; quaternion factors are never commuted.

`packet_fundamental_pin`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOnePacketMoment.lean:341`, selects
spin one at private slots 3,6,8. Spin zero vanishes by odd degree one;
all higher spins vanish by degree selection. At each step the other two
current action factors remain inside the spectator. Thus, for every K>=1,

    H24[V*chi*f^2] = (coeffW(w,1))^3 * H24[bareProduct].

`bare_moment` and `bare_moment_extended`,
`lean/YMGap/Continuum/SU2QuaternionCornerFundamentalMoment.lean:330`, `:369`,
give H[bareProduct]=1/16. Two symbolic shared-link Schur contractions
retain the entire boundary and insertion. The middle unit cancellation is
through HaarCarrierEqv, not a false coefficientwise sphere equation.
The remaining character-square integral retains the scalar-square spectator.
Only the final one-coordinate scalar-square moment is directly reduced.

`packet_moment`, `lean/YMGap/Continuum/BF4ExactSlabWidthOnePacketMoment.lean:408`,
therefore proves, for every rational w and every K>=1,

    H24[V*chi*f^2] = (1/2)*w^9.

`tester_first_independent` and `tester_project_two_zero`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOnePacketMoment.lean:101`, `:140`,
prove r is independent of blocks 0,1 and P2(r)=0 coefficientwise.
`piece_test`, `lean/YMGap/Continuum/BF4ExactSlabWidthOneSource.lean:210`,
moves the numeric prefix and fluctuation onto this adapted tester. With
tau2=(I-P2)P1P0(nu*Phi), the resulting exact joins are

    H[tau2*r] = (1/2)*w^9,
    H[tau2*f] = 0,
    H[tau2*r_shift] = (1/2)*w^9.

The declarations are `source_pair`, `source_probe_zero` and
`shifted_source_pair`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOneFringeMoment.lean:56`, `:76`, `:87`.
The adapted-tester theorem is applied BEFORE the shift: P2(r_shift)=-2f,
not zero. Conditional centering justifies the subsequent subtraction.

## Quantitative finite seed, not an ideal inverse

`hexSquareBound`, `shiftedTesterSquareBound` and
`shiftedTester_haar_square_le`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOneShiftedTestBound.lean:72`, `:81`, `:85`,
give the certified caps chi^2<=4 and H[r_shift^2]<=16. Multiply the first
certificate by the FULL original nu and f^2. The short identity

    nu*f^2*(4-chi^2) = 8*nu*f^2 - 4*nu*chi*f^2 - nu*r_shift^2

and the exact moment give

    H[nu*r_shift^2] <= 2*(1-w^9).

This is `shiftedTester_marginal_square_le` in the same module (`:171`).
The proof uses no spin-two moment, independence of the density, or discarded
action factor. Its guards are 0<w<1, headCutoff(w)<=K, and K>=1.

`fringeTest`, `lean/YMGap/Continuum/BF4ExactSlabWidthOneActualFringePairing.lean:155`,
is the existing finite `ActualSeed.test` on the actual tau2. Its defect is
D=nu*q2-tau2. `pairingTolerance` (:132) returns epsilon=w^18/256 and
`pairingDegree` (:162) computes the existing defect-approximation cutoff.
At every k>=pairingDegree, H[D^2]<=epsilon. Ordinary Haar Cauchy--Schwarz and
H[r_shift^2]<=16 give |H[D*r_shift]|<=w^9/4. Thus

    H[nu*q2*r_shift] >= w^9/4,
    H[nu*q2^2] * 2*(1-w^9) >= w^18/16.

These are `fringeTest_pairing_lower` and `fringeTest_norm_product_lower`,
`lean/YMGap/Continuum/BF4ExactSlabWidthOneActualFringePairing.lean:165`, `:197`.
The second uses weighted Cauchy--Schwarz with the SAME original marginal
certificate. Both results apply to actual finite polynomials, not to an
unconstructed inverse-density limit. Their degree depends on w and K;
there is no fixed-degree asymptotic assertion. The existing
`approximationDegreesAfter` and `approximation_bound_after`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:145`, `:159`,
permit a supplied seed floor followed by recomputation of the correction
degree; the lower test imposes no fixed old correction degree.

## Direction decision and remaining obligations

These results still do not establish a regulator-controlled family UPPER budget.

A fixed-width coupling-dependent lower calculation is not width growth and
does not rule out a permitted C(w). Do not prolong the auxiliary producer
diagnostic into an assertion that the physical route fails.

The existing reduced-action rejoin is a substantive alternative: for supported
fringe-independent inputs, `marginal_mean_active`, `marginal_pair_active` and
`energy_active`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:69`,
`:93`, `:129`, identify original mean, norm and energy with the retained
active action and the SAME terminal messages. The centered extraction already
has joint norm control and exact energy splitting:
`centered_pieces_norm_le` and `centered_extracted_energy_split`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:91`, `:139`.

Reduced-density residuals cannot simply be passed to the full-density
`test_centered`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeed.lean:125`,
or `actualResidual_corrected_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:294`.
They would need an estimate on their own actual reduced edge followed by
the existing original-energy equality. The retained active interaction is
not eliminated by this equality. The required spatial/depth/cutoff control,
physical calibration, same-theory continuum/QFT and all-group joins remain open.

## Verification boundary

Eight focused serialized checks have passed: width-one geometry, appended
oriented selection, bare corner moment, width-one source, full packet, and
source-pairing join, shifted-tester bound, and actual finite seed pairing.
All 79 printed gates (69 new, ten existing; 14 axiom-free)
are within {propext, Quot.sound}, with no final warnings/errors/sorryAx.
The monitored launcher used one worker and a 20 GiB ceiling, with a fresh
process/swap preflight for each invocation. No full-root build, full audit
or guard run is claimed. CI and machine-safety limits are unchanged.

The only elaboration-limit change is maxRecDepth=10000 confined to the fixed
literal-geometry enumeration section. It does not evaluate heat polynomials.
Initial checks exposed that depth limit, two missing explicit polynomial
arguments, missing namespace opens and an unreduced constant base-case type;
none required a mathematical change. Independent mathematical and final-source
reviews passed, including the finite tolerance, same-weight and normalization pins.
No sorry or analytic assumption was added, and no canonical frontier field
was changed. Seven new modules are imported in the semantic root; the changed
oriented-selection module was already imported. Root integration was not run.

Final focused logs and SHA-256:

```text
/tmp/ym-width-one-geometry-20260917.log
46a8fb9b36ed800ff7f37b91727d3922556f95e8390e63af92780ba4473d373d
/tmp/ym-oriented-word-degree-selection-20260917.log
b9e635273b6b77a892c7c2533a99cd59a377023a5dbb78b378730c522a922d09
/tmp/ym-corner-fundamental-moment-20260917.log
229e4f6b8f92de14631daeadcdfe4f77b7a88d45c8364678ad9f66b79d9ca318
/tmp/ym-width-one-source-20260917.log
85ae5670c0c5456201ff36153d598f0439c502ee39f761c3cc295b08acafa063
/tmp/ym-width-one-packet-moment-20260917.log
0da6deb66a09089ee8cbaba9e90b81c938bf47e8e6ca205bcb50a609c472f361
/tmp/ym-width-one-fringe-moment-20260917.log
7288219b338b9fac3694880bd4393c58dde3ea177935fb522c80b5b8fffae36c
/tmp/ym-width-one-shifted-test-bound-20260917.log
69cba993f5943202e9537d3392bceead326534fe908fe73ae3ae8b35b50ec823
/tmp/ym-width-one-actual-fringe-pairing-20260917.log
765db81a4d167b6ec1890d8a1fa1f8352a5435d88f70d40531081438ee63182c
```
