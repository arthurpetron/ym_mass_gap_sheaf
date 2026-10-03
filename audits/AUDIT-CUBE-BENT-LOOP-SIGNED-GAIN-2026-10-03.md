# Bent cube signed gain diagnostic

The complete OWN-centered signed gain has a favorable exact finite polynomial
certificate candidate on the six-face SU(2) cube at representation cutoff one
and terminal depth zero. The computed degree-68 polynomial P satisfies
P(r) >= (3/2)*r^10 for 0<r<=1/8. This is untrusted exact-arithmetic evidence,
NOT a new kernel-checked Yang--Mills theorem. The original cube matrix pin,
later-cutoff/depth passage and growing-family survival estimate remain OPEN.
Subsequent Lean work below checks the original cube source restriction and
seven-moment transport, but does NOT yet certify their numerical values or
the gain sign.

## The retained finite action and center

The new producer reuses the unchanged signed Haar contractions of
`computations/cube_cutoff_one_checkpoint.py:79` (`edge_tensor`) and `:109`
(`haar_loops`). Its original spatial matrix is `spatial_matrix:144`;
`transfer:176` retains T=D*A, not a heat-bath generator. With r=w^3,
V is the product of ALL SIX factors 1+2*r*chi_face. The 32 cycle states are
not restricted to the six plaquettes.

`computations/cube_cutoff_one_signed_gain.py:159` (`bent_loop`) selects faces
0 and 2 and their six-link outer boundary F, cycle mask 318. This bent loop
is a diagnostic observable, NOT a replacement for the existing dyadic square
anchor. `insertion_matrix:170` computes the full insertion
M_F[i,j]=H[W_i*V*F*W_j]; projecting multiplication by F before retaining V
would discard channels and is not done here.

At terminal depth n=0, g_0=1. Write U=T1, and let the weighted pairing be
ell(p)=H[V*p]. `compute_pilot:226` computes

```text
Zodd = ell(U)                    Zeven = ell(U^2)
c    = ell(U*F) / Zodd           b = T(F-c)
C1   = ell(U*(F-c)*b)            C2 = ell(b^2)
a    = r^6                      G = C2-a*C1.
```

The mean belongs to the actual odd marginal V*U/Zodd. The odd and even
partitions are distinct and are never cancelled as equal. The point
w=1/2, r=1/8 gives 2^-30 < G < 2^-29 with this center; the much larger
uncentered gain is retained only as a regression check, not a substitute.
Every face factor at this point has the separate pointwise floor 1/2.

The intended ORIGINAL finite consumer is `commutatorGain`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredCommutatorGain.lean:97`),
whose centered message is defined at `:88`. The existing completed pin is
`gainLimit_completed_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredGainLimit.lean:131`). Neither
has been instantiated with this computed matrix: that requires the source
identification and later-cutoff/depth work recorded below.

## Complete signed coefficient estimate

`polynomial_matrix:94` recomputes the rational coefficient matrices A(r) and
M_F(r) from the same guarded Haar contractions. There is no cached matrix
trust path. `compute_polynomial_pilot:137` keeps the mean numerator N and
odd partition Z as polynomials, computing

```text
U  = D*A*e0                    Z = e0^t*A*U
N  = eF^t*A*U                  bZ = Z*D*A*eF - N*U
P  = bZ^t*A*bZ - r^6*(Z*U^t*M_F*bZ - N*U^t*A*bZ)
   = Z^2*G.
```

The degree is 68, coefficients below degree ten vanish, and c_10=2.
The ENTIRE signed coefficient remainder has the exact majorant

```text
S = sum(i>10, abs(c_i)*(1/8)^(i-10))
  = 624923141201848467490810145716514015485995116321599
    / 1683649886205200161770644927289158038643634289508352
  < 1/2.
```

Thus coefficient algebra gives P(r)/r^10 >= 2-S > 3/2 throughout the stated
interval, not merely at sampled points. The leading coefficient comes from
the two lower-perimeter plaquette channels; the complete remainder and
OWN-mean corrections were computed, not dropped into an unestimated O term.
The reusable scalar interval compiler is already
`lean/YMGap/Constructive/QPolyWeightedL1.lean:42`
(`abs_eval_le_weightedL1`). No new conditional normalization or polarization
interface is needed. This turn did NOT instantiate that compiler in Lean or
prove the missing original-matrix identity.

The full exact rational coefficient list, messages, point gain and source
hashes are saved in
`audits/CHECKPOINT-CUBE-BENT-SIGNED-GAIN-2026-10-03.json`.
Read its large integer pairs without floating-point conversion.

## Original transfer boundary

Existing unguarded original-action identities support the intended bridge:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveTransfer.lean:87`,
  `original_transfer_haar_active`, gives tested ORIGINAL transfer reduction.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:69`,
  `marginal_mean_active`, retains both ORIGINAL terminal messages.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeFaceGeometry.lean:54`,
  `active_index_iff`, identifies the active indices. At width two there are
  24 active kinetic links, of which twelve belong to the cube core; the
  other twelve require an explicit independence/heat-vacuum elimination.

These declarations do NOT pin the 32-state orthonormal basis, its heat-image
closure, or the computed matrix to the original coordinate carrier. That
same open source pin was already recorded in
`audits/CHECKPOINT-01-NORMALIZED-PAIR-2026-09-18.md` and `lean/SORRY_LEDGER.md`.
No surrogate matrix has been silently substituted into a Clay-facing field.

The pilot also FAILS the existing head-cutoff guard:
`BF4ExactSlabRetainedHeatHeadComparison.headCutoff`
(`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:55`) is at
least bandSize, by `bandSize_le_deficitCutoff`
(`lean/YMGap/Continuum/BF4ExactSlabJacobiDeficitInterval.lean:72`). Definitions
`bandSize:49` in that file, `tailCutoff`
(`lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:102`),
`spacingLabelCutoff`
(`lean/YMGap/Continuum/SU2PointwiseHeatSpacingCompletion.lean:71`) and
`powBaseCutoff` (`lean/YMGap/Continuum/HeatKernelConvGen.lean:266`) give
headCutoff(1/2)>=17. K=1 cannot enter those guarded consumers. Direct finite
positivity is a different statement, not a waiver of the guard.

## Verification and next mathematical join

The focused twelve-test run passed in under one second. A separate complete
producer run took 0.860 seconds with 30,720,000 bytes peak RSS (Darwin), one
NumPy thread, 85 percent system-free memory and zero swap at preflight.
The degree cap is 80; existing degree/index/int64 and tensor intermediate
guards were unchanged. No Lean build, full audit, new axiom, sorry, canonical
field, CI or chart change occurred.

Independent review verified the stored integer data and hashes, exact tail,
floor>3/2, P(1/8)=Zodd^2*G, distinct partitions and OWN-centered messages.
The initial `/usr/bin/time -l` wrapper could not read a sandboxed clock
counter after eight tests passed; the final plain twelve-test command exited
successfully. Resource figures above use the separate producer run.

FORWARD: pin only the original messages U=T1, B=TF and their seven required
scalar moments, reusing the existing local tensor results; a complete
32-state operator model is not necessary for this gain evaluation. The
moments are Z=ell(U), N=ell(U*F), ell(B^2), ell(U*B), ell(U^2), ell(U*F*B),
ell(U*F*U). They reconstruct the same cleared polynomial directly:

```text
P = Z^2*ell(B^2) - 2*N*Z*ell(U*B) + N^2*ell(U^2)
    - a*(Z^2*ell(U*F*B) - N*Z*ell(U*B)
         - N*Z*ell(U*F*U) + N^2*ell(U^2)).
```

The numerical part of this smaller source-identification task is not yet
proved; the subsequent original-source restriction is checked below. Then
control how the favorable channels and COMPLETE signed remainder change at
later cutoffs and terminal depths. Do not iterate fixed-small-nome tests as
a substitute for that mathematical passage.
BACKWARD: retain the already checked demand for a SAME macroscopic response
ratio and relative three-norm comparison on a justified growing physical
family. This small fixed-cube bound supplies neither. Its observable, nome
range and cutoff must not be silently promoted to the dyadic square route,
continuum survival, physical mass, full QFT structure or every-group target.

## Subsequent checked original cube source restriction

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeTransfer.lean:115`,
`activeSpatialFaces_two_mem_iff`, proves the actual width-two retained faces
are exactly the six cube faces. `activeSpatialWeight_cube:176` identifies
their unchanged original heat product coefficientwise, not the FULL spatial
action coefficientwise. `cubeIndices_length:192` and `cubeIndices_nodup:187`
certify twelve distinct original coordinates.

`outgoing_core_perm:200` partitions the ORIGINAL active kinetic list.
`activeSpatialWeight_cube_independent:214` proves the retained action omits
every noncube coordinate. `original_transfer_cube:229` composes original
fringe-action peeling with exact heat-vacuum removal of the remaining
independent active factors. It retains EVERY supported output test, at
every rational nome and finite cutoff. No positivity guard is needed for
this signed equality.

`bentEdges:264` uses the precise route 0->2->3->1->5->4->0, under
vertex=x+2*y+4*z. Its inverse orientations are retained. The actual original
messages U=T1 and B=TF are identified by
`original_vacuum_message_cube:299` and `original_bent_message_cube:304`.
These are supported-Haar equalities, not free-polynomial equality or
identification with the computed 32-state expansions.

`originalBentMoments:369` and `cubeBentMoments:380` keep the order
Z,N,BB,UB,UU,UFB,UFU. `original_seven_bent_moments_cube:391` proves all
seven equalities. The proof substitutes original messages with the FULL
original spatial action still present in the supported insertion, then
peels that action using locality of the cube representatives. It does not
assume syntactic locality of the raw original messages. Unit factors and
scalar commutation do not change the moments. Z and UU remain the distinct
odd and even partitions; no mean denominator or eigenpin is supplied.

The final focused check used one worker, 12 GiB OS reserve and the mandatory
20 GiB worker cap. Its fresh preflight showed 85 percent system-free memory,
zero swap and no competing build/runner process. It exited successfully in
2.232 seconds. All 24 printed gates (17 new public theorems and seven
helper/dependency diagnostics) contain only propext/Quot.sound, with no
errors or warnings. Independent source and mathematical review passed.
Accepted log: `/tmp/ym-cube-original-transfer-20261003-final.log`.

```text
Lean source SHA256:
c0d086709fa6cadc40e853842aef9e5a9fc4f882babb2e9bcbf44c6b00d7025d
Accepted log SHA256:
83abf000636741f620aa6807b707e38d3dba59d027301a64830e134cfdbcc7a1
```

Earlier checks which contained compilation errors or a classical dependency
were rejected. The final geometry uses explicit natural-number equalities
and finite cases. No full build, aggregate/root check, axiom baseline
regeneration, canonical frontier change, CI change or ASCII reprint ran.

NEXT FORWARD: evaluate the seven literal cube moments and certify the complete
signed polynomial. A full 32-cycle range theorem is optional: source review
gives direct two-/three-slice formulas. With W2=Vx*Kxy*Vy and
W3=Vx*Kxy*Vy*Kzy*Vz, the respective insertions are
1, Fy, Fx*Fz, Fz, 1, Fy*Fz, Fy. This is a reviewed contraction plan,
NOT a new formal identity or a resource-validated computation. The concrete
tagged tensor wiring and certificate generation remain OPEN; do not expand
the full polynomial without capacity analysis. The already proved source
restriction prevents a surrogate action substitution in this next step.

NEXT BACKWARD: the SAME original macroscopic ratio and relative three-norm
costs on a justified growing physical family remain unsupplied. No new
normalization consumer is needed. Numerical positivity on this small cube,
if certified, would still not close either input or bypass the failed K=1
head-cutoff guard, later cutoffs, depth, volume or physical scaling.

## Subsequent checked original numerical fusion coefficient

`lean/YMGap/Continuum/SU2QuaternionIndependentTailMoments.lean:337`,
`fundamental_pair_moment`, proves
H[chi(U*p)*chi(U*q)*r]=H[scalar(conj(p)*q)*r] on the ORIGINAL arbitrary
quaternion carrier. Both tails have degree zero at the integrated block;
r is independent there. No mutual tail independence, unit norm, positivity
or support premise is assumed. Sixteen coordinate covariances contract the
two arbitrary tails; no concrete monomial expansion is required.

The concrete file is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeBentFusion.lean`.
`firstFace_pin:78` and `thirdFace_pin:90` recode the actual original origin
p01/p02 faces as U*A and U*B with the SAME forward origin-x link.
`bent_pin:112` and `tails_join:136` identify conj(A)*B with the precise
six-link bent word, coefficientwise, keeping its original inverse orientations.
`fTail_independent:180`, `bent_shared_independent:188` and `fTail_unit:216`
provide the actual selected-link independence and five-link Haar-unit norm.
Index separation uses original member-index injectivity, not enumeration of
the ambient carrier; face membership uses its proved geometric characterization.

`bent_square_haar:229` proves H[F^2]=1 on N=length(baseLinks 2).
`adjacent_faces_bent_fusion:252` proves
H[(firstFaceTrace*thirdFaceTrace)*r]=(1/2)*H[F*r] for EVERY insertion r
independent of the common origin-x link. It may contain all six bent links.
`original_bent_two_face_moment:272` instantiates r=F and yields exactly 1/2.
These are numerical ORIGINAL Haar contractions, not values of the full
seven weighted moments, a 32-state range theorem or an interacting gain bound.

Two final serialized focused checks used jobs=1, 12 GiB reserve and 20 GiB
worker cap. Fresh preflights showed 85--86 percent system-free memory,
zero swap and no competing build. All thirteen printed gates passed within
{propext, Quot.sound}: four new public theorems, seven concrete helpers and
two existing first/second-moment diagnostics. No errors/warnings. Independent
Sol mathematical review and Luna source/geometry review passed. The final
cube check reported about 5.0 GiB build RSS with 31.4 GiB available and no
swap. Earlier interrupted or errored attempts are NOT accepted evidence.

```text
Generic moment source SHA256:
727a31dd18da462d374bd2ce44dff2213fb665f5d1355e57cdc1de213f940a07
Concrete fusion source SHA256:
af3302bb15c363411c57de3664a0f31fd8e07948413668ac42e89261e776f99f
Generic final log: /tmp/ym-shared-link-tail-pair-20261003-final.log
SHA256: 8262bf0b70c41b3f743d175e8fadac66aa9c83b6eb252c183fcb3dcbb3de5c63
Concrete final log: /tmp/ym-original-cube-bent-fusion-20261003-final.log
SHA256: d22c8dd6e311267adccb208d07836984d048944cc830d3d00980e4a6167f4c6f
```

No full build, aggregate/root check, axiom baseline regeneration, canonical
field change, CI change or ASCII reprint. Root import is registered only.

NEXT FORWARD: join the actual six-face subset expansion to original selected
block sign-odd vanishing, leaving the singleton Q and its five-face complement
in H[P*V*F]. The remaining complement must be evaluated with arbitrary-insertion
Haar-unit cancellation, not by setting coordinate radii to one coefficientwise.
The three further half-fusions/two backtracks are a reviewed contraction plan,
NOT a checked complement value or tested-transfer polynomial. Full seven-moment
and complete signed-gain certification remain OPEN, including positive partitions
and OWN-mean joins; the cutoff-one head guard is unchanged.

NEXT BACKWARD: the source-reviewed useful numerical target is gain relative
to the SAME centered lag-one cross, not its sign alone. The complete identity
is `BF4ExactSlabFixedSpatialFilteredCommutatorGain.filtered_loop_commutator_identity`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredCommutatorGain.lean:200`;
its guarded endpoint cost is `endpointMismatch_bound:443`. Passage consumers
are `normalizedFiniteGain_approx` at
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredFiniteGainLimit.lean:111`,
`gainLimit_completed_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredGainLimit.lean:131`, and
`dyadicUnitResponse_filtered_block_floor` at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`.
The small K=1/n=0 bent channel does NOT meet their cutoff/depth/observable
inputs. The actual growing-family ratio and three relative quadratic costs,
physical scaling, full QFT and every-group endpoints remain unsupplied.

## Subsequent checked literal parity, complement and source-action channel

This increment completes the preceding two-survivor source contraction,
not the seven weighted moments or their signed gain.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeBentParity.lean:93`
(`cubeSelections_parity_checked`) checks only the incidence of the six
literal faces and twelve physical links. `badSelection_oddEdge:101`
returns the computed physical witness; `selectedBentInsertion_degree:196`
transports its exact degree through original member-index injectivity.
`badSelection_haar_zero:261` applies selected-block Fubini to annihilate
every original selected insertion except singleton Q and its five-face
complement. Thus 62 of the 64 terms vanish. No ambient polynomial, carrier
index enumeration or external arithmetic oracle is evaluated by that checker.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeBentComplement.lean:297`
(`first_fusion`), `second_fusion:321` and `third_fusion:331` integrate the
original links 67, 26 and 37, respectively. Their spectators are exactly
F*chi4*chi5, F*chi5 and F. `W_cancel:204` removes the intervening
46 and 57 backtracks ONLY in the arbitrary-insertion Haar ideal.
The final word is the cyclic inverse of the literal bent word.
`four_face_bent_moment:388` proves H[F*chi1*chi3*chi4*chi5]=1/8.
`first_square:431` integrates the repeated P with the complete remaining
spectator retained. `complement_selection_moment:492` therefore proves
the actual five-face subset moment 1/8; `singleton_selection_moment:502`
connects the other actual subset to the previously checked moment 1/2.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeBentActionMoment.lean:107`
(`survivor_filter`) checks the literal order of the two surviving rows.
`tested_bent_action_channel:113` consumes inclusive cutoff-one heat-prefix
splitting, structural scalar extraction, witnessed zero rows and both
surviving moments to prove, for EVERY rational w,

```text
H_N[(P*F)*cubeWeight(w,1)] = alpha*(1/2) + alpha^5*(1/8)
alpha = coeffW(w,1),  N = length(baseLinks 2).
```

This is the original six-face source-action integral. It is NOT yet a
tested TF identity, full original-fringe weighted join, OWN-mean value,
32-state range theorem, gain sign or completed/scaling estimate. No
positivity restriction on w is needed for this polynomial/Haar identity.
The new file checks the alpha form, not a separately printed r-form theorem.

Three final serialized focused checks passed: Parity b (11 gates),
Complement f (14 gates), ActionMoment b (2 gates). All 27 reported axiom
sets are subsets of {propext, Quot.sound}; ten new public theorem gates
are included. No errors/warnings. Independent Sol mathematical review
passed for the literal fusion words, spectators, repeated-face removal
and weighted subset sum. Independent Luna source/log/hash/diagram review
also passed; all cited declaration anchors and six hashes matched.
The safe-build skill kept these checks narrow, with jobs=1, 12 GiB reserve
and 20 GiB worker cap. Each launch had a fresh capacity/process check;
system-free percentages were 84--86 percent, swap zero. The accepted
complement check reported 4.8 GiB build RSS and 32.1 GiB available.
Earlier errored attempts, including a concrete-product recursion failure,
are NOT accepted evidence. Factoring the literal fold through a generic
opaque theorem fixed it without enlarging any limit or weakening a claim.

```text
Parity source SHA256:
54fb4bbdda971e81f91928770e12e27269e965f6bdd7242d43b46fc023ee4a94
Accepted log: /tmp/ym-cube-bent-parity-20261003-b.log
SHA256: 4cd22f6fa2de3f7f87bc0da48b56e8d84e351384ef62b29e70deb0a689f6c0a6
Complement source SHA256:
1f1c00d717239d2a152f0610268e1258b030d5ef5c0e6f017088d80f9f87b381
Accepted log: /tmp/ym-cube-bent-complement-20261003-f.log
SHA256: d9804e1c253aad0ab359c86d03569c88fae9653cc0aa934d3f0bc328a530b846
ActionMoment source SHA256:
32d3186dfa1d6bb1d55c52e12d3475188f78adcb70891b03f077d5a24c8f1276
Accepted log: /tmp/ym-cube-bent-action-moment-20261003-b.log
SHA256: fd75958690cff97dd98831b3bd91bf8c50406c5e76c90d46c6c90c19df8d1fe4
```

Root imports registered only; no aggregate/full build, axiom baseline
regeneration, CI change, canonical field change or ASCII reprint. No new
sorry/axiom, classical shortcut, native decision or external computation.
Every exact displayed chart claim remains unchanged.

### Next forward-backward join: source-reviewed Young route, NOT PROVED

A reviewed alternative to full seven-moment expansion retains the literal
finite action ell(p)=H[V*p], U=T1, b=TF-cU at its OWN odd mean and a=r^6.
The certified square ell[(b-aU(F-c))^2]>=0 can give
2*G>=C2-a^2*Q, Q=ell[U^2(F-c)^2]. An original P projection and unweighted
Haar Cauchy--Schwarz can lower-bound C2 from H[P*b], with a supplied actual
certificate V-m>=0. These inequalities and their useful bounds have NOT
been instantiated on this finite pilot.

Existing concrete interfaces (source review, not new checked producers):

- `lean/YMGap/Continuum/QuaternionHaarSquareCertificate.lean:116`,
  `square_insertion_nonnegative`, and its certificate square constructor.
- `lean/YMGap/Continuum/QuaternionHaarWeightedCauchySchwarz.lean:87`,
  `weighted_cauchySchwarz`, with supported original test/message inputs.
- `lean/YMGap/Continuum/SU2QuaternionProductHeatPositiveOrder.lean:43`,
  `haar_order`, for the actual V-minus-floor certificate.
- `lean/YMGap/Continuum/QuaternionHaarSharpCharacterInterval.lean:50`,
  `sharpCharacterInterval`, for the original Haar-unit trace caps.
- `lean/YMGap/Continuum/SU2QuaternionHaarCertificateIntegration.lean:91`,
  `partialHaarHeads_certificate`, for integrating the actual positive cone.
- `lean/YMGap/Continuum/SU2QuaternionProductHeatConstant.lean:59`,
  `productMap_one`, gives a supported-Haar unit pin; it is NOT coefficient
  equality. `lean/YMGap/Continuum/SU2QuaternionHaarCertificateReindex.lean:38`,
  `carrier_of_supported`, upgrades it with both actual support proofs.

NEXT produce the separate original vacuum channel H[P*V]=2*r+2*r^5,
both kinetic test joins, and DIRECT cutoff-one kinetic positivity and
V-minus-one/U-minus-one interval certificates at an explicit small nome.
Their product cap can control the SAME odd mean using H[F]=0 without
computing the full two-slice mean polynomial. Do not invoke headCutoff
interfaces that this K=1 pilot fails. The exact seven-moment route remains
an alternative, not a mandatory new frontier field.

Even a successful finite small-nome gain proof would not supply the
justified changing family, later-cutoff/depth control, SAME macroscopic
ratio, three normalized cross-scale costs, physical calibration or the
continuum/Clay endpoints. The bent pilot is NOT substituted for the existing
dyadic square. The proved fixed-small-nome macroscopic obstruction remains.

## Subsequent checked vacuum channel, ORIGINAL kinetic tests and direct intervals

The preceding next-input list is now partly discharged by original-source
proofs. The actual OWN odd-mean bound and gain sign are NOT discharged.

### Exact source contractions and tested transfer

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeBentComplement.lean:519`
(`first_face_square_haar`) proves H[P^2]=1 using the actual three-link tail.
`closed_cube_surface_moment:529` proves H[(P*Q)*remainingFourFaceProduct]=1/16
by applying the original adjacent-face fusion with all four other faces
retained, then the checked 1/8 bent/four-face moment.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeVacuumParity.lean:77`
(`cubeVacuumSelections_parity_checked`) checks only literal finite incidence.
`badSelection_haar_zero:202` transports the computed physical odd edge
through the original block degree and selected-block Fubini. The only
survivors are singleton P and its five-face complement [f1,Q,f3,f4,f5].
Unlike the earlier Q-tested expansion, their literal filter order is
complement FIRST, then singleton. That order is preserved in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeVacuumActionMoment.lean:150`
(`survivor_filter`); `tested_vacuum_action_channel:156` proves

```text
H_N[P*cubeWeight(w,1)] = alpha + alpha^5/16,
alpha=coeffW(w,1), N=length(baseLinks 2), for EVERY rational w.
```

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeTestedTransfer.lean:92`
(`tested_bent_transfer_pin`) and `tested_vacuum_transfer_pin:101` use the
ORIGINAL transferStep w 1 2. The test P is moved through the literal kinetic
map by symmetry; its exact four-link eigenvalue is w^12. Full original
spatial action/fringe transport precedes the exact six-face recoding.
`tested_TF_channel:110` and `tested_T1_channel:118` then consume both
checked numerical source channels. `tested_centered_channel:125` gives,
for EVERY rational w and center c,

```text
H_N[P*(TF-c*T1)] = w^12*((alpha/2+alpha^5/8)
                                  - c*(alpha+alpha^5/16)).
```

No positivity or late-cutoff guard is needed for these identities. This
does not assert that a centered observable is a kinetic eigenmode or
that c is zero. The new `bent_haar_zero` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeBentFusion.lean:279`
proves only bare H_N[F]=0 by an actual original-link first moment. It is
NOT interacting OWN odd-mean zero.

### Constructed direct cutoff-one positivity and intervals

`lean/YMGap/Continuum/SU2QuaternionFundamentalProductHeatCertificate.lean:75`
(`heatAt_certificate`) constructs the actual relative factor using its
Haar-unit quaternion word and the sharp fundamental trace cap two. Its
explicit guards are 0<=alpha and alpha*2<=1. `productHeat_certificate:105`
multiplies every literal selected factor on the shared ambient carrier;
`productMap_certificate:118` integrates that actual certificate using
ordered head-Haar integration. This is direct K=1 positivity, not use or
weakening of the all-nome headCutoff interface. Positivity permits repeated
indices; normalization below separately requires the actual Nodup guard.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeFundamentalInterval.lean:52`
(`cubeFundamentalDelta`) defines delta=(1+2*alpha)^6-1.
`cubeFundamentalInterval:141` constructs BOTH endpoints of the literal
Vcube-1 at that cap, from the actual shared-variable face remainders and
their structural telescope. Its only coefficient guard is 0<=alpha.
`cubeFundamentalCertificate:165` requires delta<=1;
`cubeFundamentalHalfCertificate:172` requires delta<=1/2 and certifies
Vcube-cap(1/2). Neither theorem claims a parameter-uniform delta.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeVacuumInterval.lean:104`
(`cubeVacuumInterval`) constructs BOTH endpoints of ORIGINAL T1-1 with
the SAME delta. Kernel coefficient guards remain explicit. Literal
productMap_one/productMap_cap use cubeIndices_nodup and the original
index-range proof. Normalization is SupportedHaarEqv, NOT coefficient
equality; carrier_of_supported has explicit support for BOTH mapped and
target endpoints before transporting their positive certificates back
to the literal original vacuum message. `cubeVacuumCertificate:144` and
`cubeVacuumHalfCertificate:151` retain their delta<=1 and <=1/2 guards.

### Verification boundary

Eight final focused serialized checks passed 59 printed gates: Fusion 11,
Complement 16, VacuumParity 10, VacuumAction 4, TestedTransfer 5,
FundamentalHeat 3, CubeInterval 6, VacuumInterval 4. Every reported axiom
set is a subset of {propext, Quot.sound}; no final error/warning is present.
Earlier errored import/environment attempts are NOT accepted evidence.
Independent Sol reviews passed the literal survivor order, contractions,
kinetic multiplier/fringe transport, explicit positivity guards and BOTH
supported-Haar normalization endpoints. Luna checks cover hashes, anchors,
allowed logs, unchanged chart fence and unchanged CI.

The safe-build skill enforced jobs=1, reserve=12 GiB and worker cap=20 GiB.
Each launch had a fresh live process/memory check, 85--86 percent system
free and zero swap. The accepted longer source checks reported about
4.7--4.9 GiB build RSS with over 30 GiB available. No full build, broad
audit, resource increase or axiom-baseline regeneration was run.

Source SHA256, in module order above:

```text
CubeBentFusion: 085cf07ed8cbf25cd6f73eb66b6bea9eb9e5890ccf7e3abc774f9eb381f61be8
CubeBentComplement: 80243613de03a4ce6cd02c21ce295460dda491c46a49ddb8dea35a6ac4a6cf24
CubeVacuumParity: 1d8637dfe045e1a078ac9efb27db17882bf3996c0bee7c36c01f82a301c8fcab
CubeVacuumActionMoment: 392bbedda814b78d08b88e97c0e96b6c4b214bac1e54bd65067190814a1e2529
CubeTestedTransfer: 7f804da8a385fd90dba58643c886e5d9329400d5d1ae570ae59e41600fafde07
CubeFundamentalInterval: e2efe278950659679d29f899378f5ef522c7fa13e07155e092457f07137c632a
SU2QuaternionFundamentalProductHeatCertificate: 4976984023b429ad11e729f237facba896dad4a261abe794e946b9be30b7db0d
CubeVacuumInterval: 53a0b4ce4183f069a28f5dc1c02ab14e3e98d398f1b80a1d5cbbe19ff3946a0f
```

Accepted logs and SHA256:

```text
/tmp/ym-cube-bent-zero-20261003-a.log
5416fcfa4625290c1f74b0f592fbe5eb55dc8138455be8e1ff19fdcb2cc8fbe7
/tmp/ym-cube-vacuum-moments-20261003-a.log
e508029ab83479fab70085d7c545c7ecebd33bf48ca36561b51e561cc73d8bb8
/tmp/ym-cube-vacuum-parity-20261003-a.log
98f53fc2478c5406d81157df949fa2619f15439c12f8e9697c06fb602334ceeb
/tmp/ym-cube-vacuum-action-20261003-a.log
9f273fe6f673129c5ee1e6c928a983933730f74ff259c18d19d58a9d71db72bd
/tmp/ym-cube-tested-transfer-20261003-b.log
e4b9190574945a7beda93ff2c2bfd04ee09976d05bcd940e4b3de2af5cbcf122
/tmp/ym-fundamental-product-heat-20261003-b.log
849d394105cdeb31b5f5cb07ef99fff1abe53071f7f0b017cd430346dd95cf9d
/tmp/ym-cube-fundamental-interval-20261003-b.log
e3b3dea31fd178b3b2986be71bae61b9b1c58c3397d7a6cb8dec0de06681c9cf
/tmp/ym-cube-vacuum-interval-20261003-b.log
3cd8da896baa42e9ca6fd1660b03bcbc0d9c6365b519b488a6595e46be3c9ce6
```

### Next forward-backward mathematical join

FORWARD instantiate the explicit small-cap guards; combine the actual
Vcube-1 and T1-1 intervals to control their product and the SAME OWN odd
mean. Use the original tested projection with Haar Cauchy--Schwarz and
the weighted Young square to prove the actual finite signed gain.
These mean/gain bounds remain OPEN; no zero interacting center is used.
All seven exact weighted values remain an alternative route, not a new
mandatory intermediate theorem.

BACKWARD retain the unsupplied justified changing-family macroscopic ratio
and normalized cross-scale comparison. The finite K=1/n=0 bent loop does
not meet their later-cutoff/depth/observable inputs and does not overcome
the checked fixed-small-nome macroscopic obstruction. Physical scaling,
nontrivial continuum survival, full SAME-theory QFT and every compact
simple group remain OPEN. Root imports are registered only; canonical
fields, exact chart fence and CI are unchanged. No ASCII reprint.

## Subsequent checked ORIGINAL OWN-centered positive finite gain

This section supersedes the preceding pending finite mean/gain statements
only at the explicit finite point below. The wider degree-68 coefficient
candidate, late-cutoff/depth, scaling family and Clay endpoints remain OPEN.

### Original source and quantitative bounds

All paths in this section start with `lean/YMGap/Continuum/`.

- `BF4ExactSlabFixedSpatialCubeOddBackgroundInterval.lean:90`,
  `cubeOddBackgroundInterval`, constructs BOTH signs of the literal
  Vcube*(ORIGINAL T1)-1 with cap 2*delta+delta^2. Its
  `bentObservableInterval` (:128) certifies the actual six-link trace cap 2.
- `BF4ExactSlabFixedSpatialCubeSmallFundamentalCap.lean:27`,
  `cubeFundamentalDelta_le_cap`, proves 0<=alpha<=1/512 implies
  delta<=1/32; `directKernelGuard_of_coeffW_cap` (:48) proves alpha*2<=1.
  `smallNome` (:59) is 1/16, with its actual coefficient equivalent to
  1/2048 (:63), positive and within the explicit cap. These are finite
  guards, not uniformity in unrestricted coupling or volume.
- `BF4ExactSlabFixedSpatialCubeOddMomentPin.lean:61`,
  `oddPartition_background_pin`, and `oddNumerator_background_pin` (:73)
  first use the seven ORIGINAL moment pins, then explicitly tested
  vacuum-message transport. They identify ell(U) with H[Vcube*U] and
  ell(F*U) with H[Vcube*U*F], retaining literal ORIGINAL U=T1.
  Original U locality is NOT assumed. `mean_odd_ratio_pin` (:94) retains
  the old edge-law mean's head guard when asserting compatibility.
- `BF4ExactSlabFixedSpatialCubeOwnMeanSmall.lean:93`, `oddPartition_floor`,
  proves Zodd>=959/1024; `oddPartition_positive` (:107) constructs its
  positive denominator. `oddNumerator_abs_le` (:114) proves
  |Nodd|<=130/1024. `originalOddMean` (:128) is Nodd divided by this
  SAME original odd partition, and `originalOddMean_abs_le` (:153)
  proves |c|<=1/4. Bare H[F]=0 is used only after the complete original
  odd-background remainder is paid. No odd/even partition identification.
- `BF4ExactSlabFixedSpatialCubeCenteredSquareProjection.lean:137`,
  `centeredSquare_projection_lower`, retains b=ORIGINAL TF-c*T1 and
  proves half*H[P*b]^2<=ell(b^2), with arbitrary c. The original spatial
  weight is retained until the supported-message square and fringe action
  transports are paid. The actual P square norm 1 and Haar
  Cauchy--Schwarz supply the projection floor.
- `BF4ExactSlabFixedSpatialCubeOwnCenteredSquareFloor.lean:96`,
  `originalOwnCenteredSquare_lower`, uses the ACTUAL odd mean to prove
  C2>=half*(w^12*alpha/4)^2. `originalOwnCenteredSquare_positive` (:119)
  is strict for positive w in the coefficient-cap regime. The favorable
  channel is alpha*(1/2-c)+alpha^5*(1/8-c/16), not a centered eigenpin.
- `BF4ExactSlabFixedSpatialCubeCenteredGainTransport.lean:80`,
  `original_commutator_gain_pin`, identifies the EXISTING
  `BF4ExactSlabFixedSpatialFilteredCommutatorGain.commutatorGain` at n=0
  with the literal original weighted b*(b-a*U*(F-c)). The square/cost/gain
  source pins (:168, :177, :186) retain original U/B under Vcube after
  composed supported tests, reduced fringe peeling and reverse tests.
  `gain_young_lower` (:216) proves C2-a^2*Q<=2G for arbitrary c/a using
  the actual cube certificate and weighted square. No gain sign assumed.
- `BF4ExactSlabFixedSpatialCubeCenteredYoungCostCap.lean:114`,
  `centeredYoungCost_sharp_upper`, proves the literal original
  Q=ell[(U*(F-c))^2] is <=(1+delta)^3*(1+c^2). Shared V/U variables are
  retained in their interval product. The paid cost pin precedes the bare
  F norm-one/mean-zero calculation. `originalOwnYoungCost_le_128` (:169)
  supplies every guard at the constructed original odd mean.
- `BF4ExactSlabFixedSpatialCubeFiniteOwnGain.lean:45`,
  `originalOwnGain_smallNome_floor`, joins these bounds to the EXISTING
  original commutator at w=1/16, K=1, width=2, n=0, a=w^18, with its
  OWN odd mean. `finiteGainFloor` (:36) is the explicit rational
  half*(half*z^2-128*a^2), z=w^12*alpha/4. At this point z=2^-61,
  a=2^-72, so the floor is 2^-124-2^-138>0.
  `finiteGainFloor_positive` (:41) checks positivity of this rational;
  `originalOwnGain_smallNome_positive` (:74) proves actual gain positivity.

This is a kernel-checked nonvacuous finite signed-gain witness, not a
certificate of the earlier candidate's whole r-range. It does not make
the old K=1 head guard true, prove a physical mass, or overcome the checked
fixed-small-nome macroscopic obstruction.

### Focused verification evidence

Nine FINAL serialized checks passed: 5+12+5+14+4+3+9+3+4 = 59 printed
gates, each with axiom set contained in {propext, Quot.sound}, and no
errors/warnings. Independent Sol/Luna mathematical/source review passed.
Every check used `scripts/safe_lean_build.py`, jobs=1, reserve=12 GiB,
check-worker-limit=20 GiB. Fresh process/memory/swap checks preceded launches;
accepted long source-join checks reported about 11.8 GiB build RSS, with
about 28--31 GiB available and zero swap. No overlapping Lean builds,
resource/proof-limit increase, full build, aggregate audit, baseline rewrite
or CI activation. An attempted launch was rejected on stale prior-process
evidence; a fresh read-only process check resolved it before retry.

Rejected development logs are NOT acceptance evidence. Corrections included
explicit carrier/namespace arguments, rational equivalence rather than raw
representation equality, coefficient recoding without rewriting dependent
reciprocal proofs, and an explicit right-fold power identity. No statement
guard was dropped to solve an elaboration problem. The existing broad audit
parser import raises `NameError: dataclass`; it was left untouched. The 59
focused output records were checked directly with the same permitted axiom
set; no repository-wide audit pass is claimed.

Source SHA256 (the preceding common module prefix applies):

```text
CubeOddBackgroundInterval: 13c7d580874e8116af2641a6a2787dee37f5a3942c65b01730d195ca9da324f3
CubeSmallFundamentalCap: 3d8ce2a24fad8066286b9c3826a746c4c8a9906893bc2af89a7b6f75203e7c5f
CubeOddMomentPin: 0db6bf9c674f1e2576b1fe0abcdb11667e98afc195adef2317269c5d327b0001
CubeOwnMeanSmall: be49f0ee1015b5ee963c8c8bcd426fdca568bbfe01405d9f6e0d687c9b5b4fa0
CubeCenteredSquareProjection: a4acf5802a1a279403311b1caa89fb26f830fb263c2fceba0383474e494707f2
CubeOwnCenteredSquareFloor: c826340a6e147f9b4f946c32fe2a3cadda596b95f00a05220cd67fd9401e6dad
CubeCenteredGainTransport: 39c2d08b661b200b69df30f150dcbf7be658c3471843ac0a26096fe87aae02a4
CubeCenteredYoungCostCap: 328354ea596dce58acbdc1048c8b35e2181ba5d0ac5b8bca0e6bf1ff5dcd2504
CubeFiniteOwnGain: 25eac9f8ac7ff47902e87c2405869899ea57319cce663f4a2d74bc5860eb99f9
```

Accepted log SHA256:

```text
/tmp/ym-cube-odd-background-20261003-a.log
0ae674bfd08e09baa30e7b7afefbde3a3b81197d87962a3cce65f5761a4279ed
/tmp/ym-cube-small-cap-20261003-c.log
790bff4a21fe4b78d24193d6e2f32f3acfd247a620858f31e0eb89773f6b9e37
/tmp/ym-cube-odd-moment-pin-20261003-c.log
3cf3ee1baa8d5d4593011458ec10c1d4fa346060c5d235f6706e8be34e7449cb
/tmp/ym-cube-own-mean-small-20261003-b.log
5d3e3bd512346094dcb869e8c35521d58e8b8aa65a4766d0581b0702cc9b9cd1
/tmp/ym-cube-centered-square-projection-20261003-b.log
f65b5f3d7c64f06c3a2d8931d36451c507f1515ff101cb3537315aabb86af907
/tmp/ym-cube-own-square-floor-20261003-b.log
e35ede3805b02425fbca250d5c1cca5a4037c6353347f2789949c9bab667d1f4
/tmp/ym-cube-centered-gain-transport-20261003-b.log
97f06cda85442606b20a443fc232a350ba7fd64741751998cdf3af6bf4cd4d0b
/tmp/ym-cube-centered-young-cost-20261003-b.log
65300a9e37297066c9b4ee433f14dfd6f39f7748031bbd81929e0cf96b1a68c8
/tmp/ym-cube-finite-own-gain-20261003-a.log
ad2c3fbf9abc31c22ed2fa53fa8f4ae6c8c5e5e2601c3d806019a3126d1e186d
```

### Next causal forward-backward frontier

FORWARD: useful original relative signed control with coupling, cutoff,
terminal depth and spatial scale varying, for the SAME scaling observable.
This finite local witness does not supply those estimates. No further
fixed-small-nome examples or generic normalization wrappers are needed.

BACKWARD: the nearest completed identity is
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredGainLimit.lean:144`,
`dyadicUnit_gain_pin`, for the actual PADDED DYADIC SQUARE and its existing
normalizer; it identifies normalized completed gain with R(2)-a*R(1).
It is not a source identity for the finite bent loop. The family-wide
macro-ratio hypothesis is still explicit in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:300`,
`normalizedBond_geometric_real_increment`. The actual hN/hplus/hminus
relative costs remain inputs of
`lean/YMGap/Continuum/BF4WilsonAllNomeThreeNormComparison.lean:313`,
`dyadic_normalized_response_compare`. None is supplied by this finite point.
Do not substitute observable shapes or normalizers without a checked join.

Justified changing family, nontrivial continuum survival, physical mass,
full SAME-theory QFT and every compact simple group remain OPEN. Root imports
are registered, not aggregate-checked. No exact displayed canonical claim
changed; chart fence and CI remain unchanged. No ASCII reprint.
