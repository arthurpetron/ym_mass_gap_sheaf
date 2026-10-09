# Adaptive directions at the original conditional-score frontier

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms,
and a finite strictly positive physical Hamiltonian mass gap.

## CHECKED original common-frame first jets and own-vector synthesis (2026-10-09)

Previous goal turn was PROGRESS: the all-degree original polynomial-kernel
normalizer and concentration identities were checked and pushed as bca66e60.
Those J04 inputs do not pay MAIN signed cost. This turn produced the initial-
source common-frame derivative required by the exterior-pair reduction below.

The bounded MAIN producer now passes: on the actual fixed spatial face,
write q0=U0, q1=U1, q2=conj(U2), q3=conj(U3), P=q0*q1*q2*q3. The physical
LEFT derivative at slot r has common prefix F0=1, F1=q0, F2=q0*q1*q2,
F3=P and sign +,+,-,-. `original_paired_first_jet`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteCommonFrame.lean:528`,
produces arbitrary-insertion HaarCarrierEqv between
the actual paired scalar derivative and scalar[(sign*F*e_i*conj(F))*P],
including the original plaquette/physical-index join. The analytic mixed-link
Hessian consumer does NOT yet exist; its immediate consumer is the recorded
PAPER own/exterior cancellation, not an assumed weighted estimate.

The next contraction is also CHECKED: `ownVector_exact`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteOwnVector.lean:273`,
synthesizes the three ACTUAL paired scalar derivatives against their signed
common-frame vectors to -Im(the ORIGINAL plaquette), at EVERY physical slot.
Its `conjugated_basis_contraction_cleared:197` first proves the coefficient
identity for arbitrary f,P with norm(f)^2 retained. Three explicit conjugated
basis rows and their nine quartic Gram identities replace one large expansion.
`prefix_unit`, CommonFrame `:162`, is used twice to remove that norm square.
No unit-P premise, assumed adjoint orthogonality or analytic interface is added.
Scalar X has normalization one; chi_1=2X gives gradient factor TWO, whereas
a bracket containing TWO such velocities gives factor FOUR. The full mixed-link
Hessian and source-specific weighted payment are still OPEN.

Available inputs: LeftRightAngularAction.coordinate_action:164,
conjugate_coordinate_action:363, frameDerivativeAt_mul:277,
other_coordinate_action:412; FaceSelection.plaquette_fourWord:61; actual
physical index injectivity; PairedFrameAt.pairedDerivativeAt_carrier:71;
and arbitrary-insertion sphere radius. All are in lean/YMGap/Continuum/.
An independent reader confirms the inverse-prefix convention. Actual derivatives
are formed before coefficient/carrier promotion; unit-prefix cancellation is
produced, not a raw padded coefficient identity or a derivative of a carrier
equality. Two bounded Sol leaves and complete ROOT/independent final-source/log
reviews PASS. Root-only serial capped checks followed fresh dynamic memory,
swap and filtered compiler/test/runner inspection EACH time. No foreign host
process was stopped; no full-tree audit, guard or resource-limit increase.
MAIN warmed/weighted payment, scaling and Clay remain OPEN.

Final evidence:

- CommonFrame check3: terminal exit 0, 2.59 seconds; all five printed gates
  exactly {propext,Quot.sound}. Source SHA-256
  `b9b5b282d469dcf8a902d1e70e8fdb6b573079614a611bf285e6e34484c25fb2`;
  `/private/tmp/ym-oct9-plaquette-common-frame3.log` SHA-256
  `a3ff57e17c9e23a7cae37da35c860ca795e9145725325a60b87c7041b04f63ef`.
- OwnVector check2: terminal exit 0, 2.33 seconds; both printed gates exactly
  {propext,Quot.sound}. Source SHA-256
  `6821b4c320b023c14c886442ef794cac9975c53f1b87407af6476d2782df1845`;
  `/private/tmp/ym-oct9-plaquette-own-vector2.log` SHA-256
  `12ba2ccaf7f8027d84e37fe557f865b413558ffd77a524dfb9375ce6a20bc362`.

Exact commands (repository root):

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteCommonFrame.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteCommonFrame.olean --log-file /private/tmp/ym-oct9-plaquette-common-frame3.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteOwnVector.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteOwnVector.olean --log-file /private/tmp/ym-oct9-plaquette-own-vector2.log
```

CommonFrame's first two checks failed elaboration (reserved name, dotted
identifiers, oversized reassociation certificate); OwnVector's first check
failed six coefficient-transport argument orders. Their repaired final checks
supersede that error output; it is not proof evidence. No `sorry`, new axiom,
classical construction or premise was added. NEXT is the genuine signed weighted
three-face/payment estimate, retaining full W, both messages, OWN warmed variance
and both chronological masses, or direct SAME-source macro retention. The parity
and summed-face PAPER screens below prune two automatic cancellation shortcuts.
Root imports are registered, not root/tree audited. Canonical displayed claims
unchanged: no chart reprint or physical/Clay closure.

### PAPER parity screen: retain the odd density response

ROOT and an independent reader checked a different pairing from physical
word reversal. Let iota conjugate EVERY physical link, and define
W_+=(W+W o iota)/2, W_-=(W-W o iota)/2, and similarly B_+, B_-.
Iterated original Haar invariance gives

    H[W*B] = H[W_+*B_+] + H[W_-*B_-].

The source input is `quaternionHaar_conjugateQuaternionBlock`,
`lean/YMGap/Continuum/SU2QuaternionSelectedHaarTranslation.lean:441`;
`conjugateQuaternionBlockPolynomial_supported:431` retains actual support.
No new parity theorem or ORIGINAL mixed-link bracket declaration is claimed.
On the cubic fixture recorded below, the PAPER calculation gives
B_+=-lambda*c*s^4*(1+2*c^2) and
B_-=-lambda*c^2*s^3*(c^2-s^2). Only the even-density summand loses its
cubic part; the odd-density--odd-bracket moment is not eliminated.

The original spatial density is NOT invariant under iota. At one literal
face put U0=c+s*i, U1=c+s*j, U2=c+s*k, U3=1, c^2+s^2=1.
The +,+,-,- word has scalar c^3+s^3, whereas all-link conjugation gives
c^3-s^3. For the actual K=1 heat prefix 1+4*w^3*X, the ORIGINAL minus
conjugated value is 8*w^3*s^3.
At w=1/4 the HEAT PREFIX has the strictly positive floor 15/16 on unit
scalars; positivity does not repair the symmetry. This is an early-prefix test, NOT a
headCutoff-admissible or original full odd-marginal counterinstance.
Distinct-face overlap already proved below means every other face meets at
most one of the three changed links; with remaining links one, its scalar
is unchanged. Literal original definitions: `plaquette:66` and
`spatialWeight:70`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean`;
`heatPrefix:31`, `lean/YMGap/Continuum/QuaternionHaarHeatCertificate.lean`.

For the REQUIRED W=V*a*b, a=g_n and b=g_(n+1), its odd part retains
V_-*a_+*b_+ + V_+*a_-*b_+ + V_+*a_+*b_- + V_-*a_-*b_-.
Both chronological message responses remain. The existing gauge laws
`plaquette_gauge_character`,
`lean/YMGap/Continuum/SU2QuaternionHaarGaugeCancellation.lean:139`, and
`terminalMessage_gauss_zero`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGaussTransfer.lean:585`,
do not bound these odd parts. A useful extra-order claim still needs a
produced local-gauge/action-message and bad-region payment relative to OWN
variance; no such bound or warmed-source locality was found. Prune automatic
oddness cancellation, retain this lossless pairing only with its residual.

### PAPER summed-face screen: no automatic cyclic cancellation

ROOT and the independent reader also tested the FULL spatial action-face
bracket sum, not only one target face. In the shifted-k fixture below,
the only nonidentity spatial faces for base >=2 are
p01(0), p02(0), p12(0), p01(e0), p12(e0). Give these scalar source
coefficients alpha,beta,gamma,delta,epsilon. At leading order the added
two source faces change the physical velocities at U1(e0), U2(e0) to
s*[alpha*i-(alpha+delta+epsilon)*k] and s*[beta*j+epsilon*k].
The five coefficients of s^3 in v_p dot B_p are respectively

    (delta+epsilon)*(beta+gamma)-beta*gamma,
    epsilon*(alpha+gamma)-alpha*gamma,
    -alpha*beta, 0, -alpha*beta.

All coefficients one give +2*s^3+O(s^4); the literal fundamental-character
source multiplies this by four. Every other face has identity holonomy
and zero scalar angular gradient at this unit field. Therefore this is
also a test of the uniform ALL-spatial-face INITIAL source, with required
ambient padding, not just three coefficients matched to part of the action.
Common-prefix corrections are O(s^2) in each velocity and cannot change
the cubic term. A common smooth radial action derivative with endpoint
value C multiplies that term by C since X_p-1=O(s^2).

These are independently checked PAPER common-frame calculations, not a new
Lean differentiated instance or a sign of the full Hessian/weighted integral.
The actual incidence and generator pins are `faceCoherentTail`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:75`,
and `coordinate_action:164`/`conjugate_coordinate_action:363`,
`lean/YMGap/Continuum/SU2QuaternionLeftRightAngularAction.lean`.
Prune automatic pointwise zero of the action-summed bracket by cyclic/Jacobi/
Bianchi reasoning; retain curl credits, full W, both chronological messages,
OWN variance and the missing signed weighted payment. No warmed-source or
scaling conclusion follows.

## Selected source-specific bracket reduction and independent kernel input (2026-10-09)

Previous turn was PROGRESS: exact finite unit-word commutator formulas and
the opposite-sign fixture were checked and pushed; the original weighted
mixed-link estimate remained OPEN. This turn returns to that estimate rather
than treating arbitrary frozen directions as the actual observable gradient.

New PAPER reduction, independently reviewed: for the actual word
P_p=Q_0*Q_1*Q_2*Q_3=(X_p,v_p), physical left velocities transport as
L_r=epsilon_r*Ad(F_r), with F_r the preceding word for positive links and
the preceding word INCLUDING Q_r for inverse links. The gradient of the
own scalar source c_p*X_p has transported velocity -c_p*v_p at every slot.
Therefore v_p dot sum_(r<s)(a_r cross a_s) contains no own-own or own-exterior
term. Exterior contributions alone remain. If each distinct other face shares
at most one edge with p, its self-pair also vanishes: the first possible term
uses TWO exterior faces touching DIFFERENT edges of p. This is not the scalar
same-link `shared_cross` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentFullAngular.lean:370`.

Scope: this locality argument concerns the INITIAL, unwarmed `spatialSpan`
gradient. It does not establish locality of the transmitted/warmed source b.
Repeated faces and signed coefficients remain; identical face contributions
must be combined without dropping their occurrences. The full original density
W=V*g_n*g_(n+1), OWN variance and BOTH chronological masses remain unpaid.

### Two source-specific tests (PAPER, not new Lean differentiation)

The existing word reversal is `reverse_word_conjugate`,
`lean/YMGap/Continuum/BF4ExactSlabSpatialAxisSwapWord.lean:43`; actual weighted
Haar swap is `originalChainAction_weighted_haar_swap`,
`lean/YMGap/Continuum/BF4ExactSlabSpatialAxisSwapAction.lean:169`. They do not
cancel the bracket by oddness. Under inversion the correctly reversed physical
velocities are a_bar_r=-Ad(P^-1)*a_(3-r), so b_bar=-Ad(P^-1)*b and v_bar=-v.
Since Ad(P^-1) fixes v, v_bar dot b_bar=v dot b. Reversing only an isolated
trace while leaving the source gradients and weight fixed is not this symmetry.

An independently checked PAPER fixture uses spatial p01,q02,r12 at the origin
(time is x3). Set outgoing U0=1, U1=c+s*i, U2=c+s*j, all other links 1,
with c^2+s^2=1. The initial scalar source F=X_q+lambda*X_r gives physical
xi0=s*j and xi1=lambda*(-c*s*i+c*s*j+s^2*k). For p, a0=s*j and the inverse
slot has a3=-Ad(P_p)*xi1=lambda*(c*s*i-c*s*j+s^2*k). The other slots vanish.
Thus v_p dot(a0 cross a3)=-lambda*s^4, or -4*lambda*s^4 for the literal
fundamental-character source. Rational stereographic c,s produce arbitrarily
near-flat instances of both signs. OWN scalar centering leaves gradients
unchanged. This is a bracket component, not the complete Hessian or an
original integrated-sign claim. Its fourth order is a property of this fixture,
not a proved order for all source families. The arbitrary-velocity first-order
obstruction does not by itself exclude improved source-specific error budgets.

A second independently reviewed PAPER fixture tests that degeneracy. Change
only the shifted p-slot U1(e0) to c+s*k; it belongs to neither q02 nor r12, so
the physical source gradients are unchanged and its own source velocity is zero.
Now P_p=(c^2,-c*s,-s^2,c*s), and the same correct inverse-prefix transport gives

    v_p dot(a0 cross a3)
      = -lambda*c*s^3*[c*(c^2-s^2)+s*(1+2*c^2)].

For c approaching 1 and s approaching 0 the leading order is cubic, not
quartic (again four times this for the fundamental source). Thus the preceding
quartic fixture cannot justify a universal fourth-order allowance. Both tests
retain literal initial closed-loop gradients, but neither proves the original
weighted expectation, the full Hessian sign, a warmed-source law or a scaling
bound. The source-specific cancellation still reduces the first possible
bracket to a three-face interaction; its signed weighted payment remains OPEN.

The actual coherent-tail word recoding is `actual_face_tail_recode`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:183`;
the selected-link scalar square is `plaquette_paired_gradient_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteGradient.lean:85`.
Neither supplied the required common-frame vector pin or cross-link Hessian
at this earlier screen. The first-jet and own-vector pin is NOW supplied by
CommonFrame/OwnVector above; the cross-link Hessian remains OPEN.
Gauss equality is arbitrary-insertion HaarCarrierEqv, not just a
single unweighted integral; derivative compatibility cannot be dismissed.
It still does not identify a horizontal mixed-link payment.

Source-only next-producer screen (ROOT and independent reader): do NOT rederive
the coordinate frame. `coordinate_action`,
`lean/YMGap/Continuum/SU2QuaternionLeftRightAngularAction.lean:164`, already pins
ALL FOUR original components to J_i U=e_i U when right=false, with no factor
one-half or unit assumption. `conjugate_coordinate_action:363` pins
J_i conj(U)=-conj(U)*e_i, and `frameDerivativeAt_mul:277` is actual Leibniz.
These are common-padded coefficient identities, not a license to differentiate
arbitrary padded equalities. `angular_coordinate_carrier`,
`lean/YMGap/Continuum/SU2QuaternionAngularCoordinate.lean:73`, and
`angularDerivative_blockIndependent_zero`,
`lean/YMGap/Continuum/SU2QuaternionHaarTailDerivative.lean:235`, supply actual
coordinate and independent-tail first jets. The public `paired_first_jet`,
`lean/YMGap/Continuum/SU2QuaternionPairedScalarSquare.lean:57`, gives individual
components for the actual two-link relative word. The general independent-tail
`linear_derivative:178` and `fundamental_derivative:227` in
`lean/YMGap/Continuum/SU2QuaternionIndependentTailAngularSquare.lean` are PRIVATE;
their public outputs package square sums.

The original common-prefix pin selected at this earlier screen was
J_(l,i) X_p = -v_p dot[epsilon_l*Ad(F_l)*e_i], with the actual positive/inverse
slot, supported physical prefix and arbitrary original Haar insertion retained.
`chain_pairedDerivativeAt`,
`lean/YMGap/Continuum/SU2QuaternionPairedFrameAt.lean:105`, moves block labels;
it is not this field-dependent prefix transport. Reuse the existing finite
derivation before building a new bridge. The finite pin is now CHECKED above;
the weighted estimate is still OPEN. No new Lean proof or weighted estimate
is claimed by this source screen.

Selected MAIN geometric input: prove that two DISTINCT common boundary edges
determine one canonical Z4 plaquette. The existing `edgesOf` and `edge_complete`,
`lean/YMGap/Continuum/ClusterCount4DProgress.lean:147` and `:207`, and
`edgesOf_nodup`, `lean/YMGap/Continuum/Z4UnitCubeIncidenceParity.lean:25`,
supply the literal nonperiodic geometry. Expected output: for distinct p,q,
any two common edges are equal; no overlap premise is to be assumed. Downstream
use is the source-specific exterior-pair reduction, whose full analytic consumer
does NOT yet exist. Proof plan: canonical plane/direction cases and exact natural-coordinate
offset equations. One bounded geometry leaf, no action/rate/frontier change;
revise if the stated canonical geometry admits a counterexample. No torus
or periodic-identification theorem is asserted.

Observed geometry producer: `two_boundary_links_determine_face`,
`lean/YMGap/Continuum/Z4DistinctPlaquetteIntersection.lean:24`, and
`common_boundary_links_equal_of_faces_ne:52` now prove the exact overlap input.
Focused check1 terminal exit 0; all three gates exactly {propext,Quot.sound},
no diagnostics/sorryAx. ROOT and independent reviewer read COMPLETE frozen
source and accepted log; independent review PASS. Source SHA-256
`2f551fb559239dec42e0b746a9bbf1a8f06471f2e909a219f6702a2cff7d0031`;
accepted `/private/tmp/ym-oct9-plaquette-intersection1.log` SHA-256
`dc9ece76fee40c29014b4d6021babdf2022c532f5a10859fe8d2685f3ef52fbf`.
Exact command:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/Z4DistinctPlaquetteIntersection.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/Z4DistinctPlaquetteIntersection.olean --log-file /private/tmp/ym-oct9-plaquette-intersection1.log
```

Fresh launch preflight: 86% free, zero swap and no competing compiler/test/runner.
One capped serial worker and unchanged reserve/thresholds; root registration
only, no root/tree audit. This pays only canonical face overlap, not the PAPER
vector pin or signed original-law estimate. Canonical chart claims stay OPEN;
no ASCII reprint.

Selected parallel J04 input: prove the recorded polynomial-kernel recurrence,
positive normalizer and squared-chord payment 6/(m+3) for all natural m, from
actual one-block Haar, angular IBP and the arbitrary-insertion sphere relation.
Test m=0 separately and m=1,2 against literal moments. One leaf, no continuous
Haar premise, source/normalizer substitution or assumed recurrence. Stop if
those finite inputs do not suffice. ROOT handles capped serial checks after
complete frozen-source review and fresh dynamic capacity; no concurrent compiler,
full-tree audit or resource increase. Both selected outputs are finite inputs,
not continuum survival, physical calibration, QFT, every-group or Clay closure.

### Observed all-degree polynomial-kernel concentration

`kernelMoment_recurrence`,
`lean/YMGap/Continuum/SU2QuaternionPolynomialKernelConcentration.lean:316`,
proves the exact recurrence for EVERY natural exponent, including m=0.
`kernelPower_certificate:72` constructs each actual kernel's positivity
certificate; no pointwise positivity field or continuous Haar is assumed.
`normalizer:400` is the finite product of computed ratios, strictly positive
by `normalizer_positive:404`; `kernelMoment_normalizer:408` and
`kernelMoment_positive:430` identify and prove positivity of the ORIGINAL Z_m.
`chordMoment_exact:472` and `normalizedChordMoment_exact:504` prove the
exact squared-chord moment `6/(m+3)` with that SAME normalizer.
`small_m_regressions:510` checks actual moments at m=0,1,2.

Final focused check3 terminal exit 0 in its initial call; all 13 public gates
exactly {propext,Quot.sound}, no diagnostics/sorryAx. ROOT read the COMPLETE
final 529-line source and log; independent COMPLETE source/log review PASS.
Check1 failed on namespace resolution, explicit coefficient transports,
unresolved polynomial arguments and raw Int.ofNat arithmetic; check2 retained
six ambiguous carrier field-notation sites. Explicit namespaces, carrier
operations, supplied reciprocal positivity and Nat-to-Int coercions repair
only elaboration, not the mathematical statements or assumptions. Failed
check1/check2 sorryAx output is NOT accepted evidence.

Final source SHA-256:
`0736ff551074eb1c8001408a84222b98c39f63ea800425bd98b23eedcb0dc764`.
Accepted `/private/tmp/ym-oct9-polynomial-kernel3.log` SHA-256:
`3105b146cc85120bf135ab38e4eb4258e670f7cc0cc04a9456dcd7337be48816`.
Superseded check1/check2 log hashes respectively:
`c8cc7aed045c29162d38be7f236a3380774ad0a6dd77538ecabc26ff1652b823`,
`cc1a5e2f57e3a10cee8c991af843c89b04b5dc6403ea3e93c08f85f2a14ad7ac`.
Exact accepted command:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/SU2QuaternionPolynomialKernelConcentration.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/SU2QuaternionPolynomialKernelConcentration.olean --log-file /private/tmp/ym-oct9-polynomial-kernel3.log
```

Each fresh preflight showed 86% free, zero swap and no competing compiler/test/
runner. Checks were serial with one 20-GiB worker, unchanged reserve/thresholds;
no resource increase, foreign code, new hole or analytic premise. Root import
is registered, not root/tree audited. This is an independent finite input for
the J04 Haar/approximation route, not an assumed continuous-Haar argument or
MAIN signed retention. Approximation/extension for arbitrary continuous
Point-functions, full compact-group realization, scaling/physical/QFT/all-
groups and Clay closure remain OPEN. No canonical chart claim changes or
ASCII reprint.

## Checked finite commutator test / PAPER mixed-link budget (2026-10-09)

MAIN mathematical question: can a global mixed-link curvature estimate replace
the local nome-dependent allowance using only the squared summed transported
directions? No such cross-link consumer exists in the current source; the
existing `plaquette_frozen_hessian`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFrozenHessian.lean:238`,
is a single-selected-link identity and retains the individual direction squares.
This test must not be used to rewrite that checked theorem or infer a new
interacting estimate.

Available inputs: actual Hamilton multiplication/conjugation in
`lean/YMGap/RepTheory/RationalQuaternionUnitNormGroup.lean`, the unit stereographic
constructor in `lean/YMGap/RepTheory/RationalQuaternionSphereNets.lean:153`, and reflected
rational polynomial identities. For the unit rotations r_i=(c,s*i),
r_j=(c,s*j), c=(1-t^2)/(1+t^2), s=2*t/(1+t^2), ROOT and an independent reviewer
derive the commutator coordinates
(1-2*s^4, 2*c*s^3, -2*c*s^3, 2*c^2*s^2). For a unit base
P=(p0,0,0,p3), its fundamental trace defect is exactly

    (1+t^2)^4 * (2*scalar(K*P)-2*p0)
      = -64*p0*t^4 - 16*p3*t^2*(1-t^2)^2.

Swapping i,j reverses the latter sign. The literal four unit links
(r_i,r_j,r_i,conj(P)*r_j) give K*P in the +,+,-,- plaquette order.
Although the transported first-order axes sum to zero, a bracket/curvature
term survives at order two whenever p3 is nonzero. Predicted finite test:
q=t=1/10, P=stereographic(0,0,q), gives opposite strict signs in the two
orders. The derivative interpretation +/-32*p3 is PAPER only; the selected
Lean output is the exact rational defect and actual unit-word pin, not a
formal analytic Hessian theorem or an original-weighted expectation.

Decision before verification: exclude a curl-only replacement if this exact
test passes; retain the nonabelian bracket term in any global-curvature route.
Keep MAIN complete signed payment/direct multi-step retention co-primary.
One small algebraic leaf, root-only narrow capped serial check, independent
complete source review; no new analytic interface, premise, sorry or raised
limits. Revise/stop on a missing genuine unit-word pin, not a surrogate proof.

### Observed finite certificate and verification boundary

`axisCommutator_closed`,
`lean/YMGap/RepTheory/RationalQuaternionCommutatorDefect.lean:86`,
proves the symbolic raw Hamilton coordinates, retaining the radius defect
before unit normalization. `trace_defect_unit:125` uses the explicit unit
relation; `plaquetteWord_pin:202` and `rotatedPlaquette_pin:226` identify the
genuine four-link unit word. `actualDefect_formula:235` and
`actualDefect_cleared:262` prove the exact rational formulas above for BOTH
orders and arbitrary rational t,q; `tenth_opposite_signs:280` proves the
predicted strict signs by kernel computation. ROOT read the COMPLETE final
297-line source; the independent COMPLETE final-source/log review passed.

Before compilation, both source readers caught and repaired a missing second
(1-t^2) factor in the private false-branch polynomial expression. Check1 then
failed on an unavailable addition-congruence name and positivity-dependent
denominator rewriting. The repairs compose the available congruences and
transport the whole reciprocal by equality elimination, with no changed
mathematical statement. Check1's diagnostics/sorryAx output are NOT accepted
proof evidence. Check2 completed exit 0 in its initial call; all 13 public
gates report exactly {propext,Quot.sound}, with no diagnostics/sorryAx.

Final source SHA-256:
`ee86c570ba11f8f7157de1879805b95b6a58857cd19215cffd996c6c181dcf88`.
Accepted `/private/tmp/ym-oct9-quaternion-commutator2.log` SHA-256:
`d769b46c0a11477d3374d662514d8c0655b4dcc95892cf788842d5b5b59b0231`.
Superseded check1 log SHA-256:
`03a8003881931ae77dcfb66a2663e28be649dab0a1ffce0b2529f6130dacccee`.
Exact accepted command:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/RepTheory/RationalQuaternionCommutatorDefect.lean --check-output lean/.lake/build/lib/lean/YMGap/RepTheory/RationalQuaternionCommutatorDefect.olean --log-file /private/tmp/ym-oct9-quaternion-commutator2.log
```

Fresh preflight before check2: 86% free, zero swap, no compiler/test/runner;
one capped worker, existing reserve/thresholds, no concurrent build or limit
increase. Root import is registered, not root/tree audited. No original BF4
RatPoly/action pin, heat-weighted expectation, analytic Hessian, derivative
or scaling theorem is established. Interpretation: retain the bracket in
the PAPER global-curvature candidate; the actual weighted payment remains
OPEN. Canonical chart claims unchanged, so no ASCII reprint.

### What a valid mixed-link replacement would still have to pay (PAPER)

For FROZEN transported pure-imaginary velocities a_0,...,a_3, the path convention
is P(t)=exp(t*a_0)*...*exp(t*a_3)*P. Write s=sum a_r and
b=sum_(r<v)(a_r cross a_v), with P=(X,pv). Direct Hamilton algebra gives

    X' = -pv dot s,
    X'' = -X*|s|^2 - 2*pv dot b.

Thus for L=log h the formal chain Hessian is
L''*(pv dot s)^2 - X*L'*|s|^2 - 2*L'*(pv dot b).
If L''<=0 and the scalar radial cost satisfies
X*L'-(1-X^2)*L''<=C_radial, the lower budget is

    -C_radial*|s|^2 - 3*|L'|*sqrt(1-X^2)*sum_r |a_r|^2.

The factor three uses sum_(r<v)|a_r|*|a_v|<=3/2*sum_r|a_r|^2.
On X>=delta>0, with L'>=0, its bracket coefficient is at most
3*C_radial*sqrt(1-X^2)/delta. This is a DEFECT-WEIGHTED cost, not a zero
cost for balanced directions or a scaling bound. ROOT and an independent
reviewer agree on the algebra and variation convention; no analytic
exponential, derivative or mixed-link theorem is certified by this screen.

The existing scalar producer is `heatRadialExpression`,
`lean/YMGap/Continuum/JacobiHeatRadialMomentJets.lean:258`, with
`heat_radial_nonnegative_nearFlat`,
`lean/YMGap/Continuum/JacobiHeatRadialProducedBound.lean:100`, on ALL of [-1,1]
at its finite-prefix guard. `heat_logConcavity_certificate`,
`lean/YMGap/Continuum/JacobiHeatLogConcavity.lean:372`, certifies the Jacobi
discriminant. These are not original character-prefix logarithmic derivatives.
The existing original-prefix curvature certificate,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.lean:104`,
covers all nine ordered jets WITHIN one selected link, not cross-link jets.

Missing joins: actual mixed physical-link jets; frozen-path/frame transport
without differentiating frozen coefficients; original prefix jet/sign or
absolute-slope error control; both terminal messages and complete original
density; and an original source-weighted bracket-defect estimate including
the non-near-flat region. An unweighted one-face heat moment cannot pay the
velocity-weighted bracket term automatically. Do not add a global-curvature
interface until its quantitative payment on the changing source is supplied.

An additional independently reviewed PAPER test fixes the required defect
order. The cleared trace numerator's quadratic coefficient has magnitude
16*p3, whereas the squared holonomy-vector defect is p3^2. For ANY rational
C>=0, the computed q_N=1/(N*(1+C)), N>=1, gives
p3=2*q_N/(1+q_N^2)>0 and C*p3<2<16, hence 16*p3>C*p3^2.
Taking N large makes these bases arbitrarily near the identity. Thus a
pointwise absolute quadratic-defect payment cannot replace the linear bracket
term. This coefficient argument is not kernel-checked derivative calculus
or an original heat expectation; improving its order would require an actual
signed weighted cancellation, not dropping the nonabelian term.

## Checked finite completed-Point Haar translation (2026-10-09 UTC)

The parallel J04 producer now removes the fixed-RATIONAL-multiplier
restriction for finite polynomial moments on the SAME completed group:

- `evalRC_coeffEqv_supplied`,
  `lean/YMGap/Continuum/SU2QuaternionPointPolynomialHaarTranslation.lean:128`,
  evaluates finite multivariate coefficient equalities through supplied CReal
  rows without choosing representatives.
- `pointEval_coeffEqv` (:171) descends through the existing Point coordinates.
- `completedTranslatedHaar_invariant` (:207) proves that exact head Haar of
  the translated polynomial, evaluated at ANY actual Point multiplier,
  equals the RC embedding of the ORIGINAL one-block rational Haar moment.
  Every degree and both Hamilton orders are covered, with the necessary
  `SupportedQuaternionBlocks 1 p` guard retained.
- `completedTranslatedEval_action` (:292) identifies the unintegrated two-Point
  evaluation with pointEval at ACTUAL completedMul g*x or x*g. It uses
  `completionMap_mk`, the actual multiplication.mapCauchy and existing rational
  Hamilton identities. No new group law, norm or integration law is substituted.

The short proof uses quotient induction, applying the checked rational theorem
at each supplied unit-quaternion row entry. RC evaluation is finite algebra,
not an arbitrary continuous-function integral. Irrational translated coefficients
cannot be passed to the unchanged `quaternionPolyLinkHaar.h : RatPoly -> Q'`.
No assumed Haar field or extra analytic premise is introduced. Existing rational
central-sign, equatorial and nonunit regression declarations are retained.

Final source: 338 lines, SHA-256
`278fdf4394a56ad90d22fa6e9384248582db692ae8ced90477e727c421caab35`.
Final check2 log: `/private/tmp/ym-oct9-point-polynomial-haar2.log`, SHA-256
`07d8823cb9b57ee9716aeac04917dc22c9044988b382308a4535721efa7e2e78`.
The monitored launcher returned exit 0; all four printed gates are exactly
{propext,Quot.sound}, with no diagnostics or sorryAx. COMPLETE independent
final-source/log review PASS and ROOT inspected the full source and repairs.
Check1 failed at four definitional bridges: two closing evaluation reductions
and exposing the completedMul representative in both orders. No limits or
mathematical hypotheses changed. The final successful host preflight found
87% free memory, zero swap and no competing compiler/test/runner. One serialized
20-GiB check worker, 12-GiB reserve; no full/root/tree audit or baseline refresh.
Root import registered. Continuous Haar, compactness, J04 and physical/Clay
closure remain OPEN; no canonical chart claim changes.

## MAIN signed-plane profile screen (2026-10-09, PAPER only)

ROOT and an independent reviewer tested an alternative ORIGINAL family, not a
replacement for `afPaddedZeroMomentumTrajectory`. For the cube of base points
0<=a_i<B, B<width, take coefficients +1 on p01, -1 on p02 and zero on p12.
At the all-one field, every incident `faceCoherentTail` is one, so interior
aggregate tails are (0,2,-2) in directions x0,x1,x2. For general constant
plane coefficients (a,b,c), their summed amplitude is

    16*((a+b)^2+(a+c)^2+(b+c)^2)
      = 16*(a^2+b^2+c^2+(a+b+c)^2).

No nonzero constant profile kills all three directions. The zero-sum plane
sector reduces this amplitude/coefficient-square ratio by four versus equal
coefficients, but the odd-profile FULL count is still 32*B^3-8*B. ROOT checked
the boundary count: x1/x2 tail-square sums are each (4*B-2)*B^2; x0 contributes
(4*B-2)*B, and amplitude is four times their sum. These are PAPER consequences
of `aggregateCoherentTail` (:92) and `family_coherent_row` (:383),
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean`, not new
kernel-checked geometry or interacting moments. Flat gradients vanish; amplitude
is not gradient energy. For B>=2, at one interior x1 link U=i with every other link one,
the two incident p01 characters give incidentSpan=4*x0, tail=2 and Gamma=16.

The actual signed family carrier is `familyState` and `source_family_span`,
`lean/YMGap/Continuum/BF4WilsonPlaquetteFamilySourcePin.lean:69` and `:92`.
The existing `excitation_swap_odd`,
`lean/YMGap/Continuum/BF4WilsonAllNomeAntisymmetricPlaquette.lean:179`, is the
origin two-face source, not this large-cube profile's produced symmetry pin.
`swap_spatialFaces_perm`,
`lean/YMGap/Continuum/BF4ExactSlabSpatialAxisSwapGeometry.lean:191`, supplies
finite geometry, not the missing source-weighted chronological estimate.
Decision: do not implement a profile-cancellation shortcut or replace the
canonical AF source. Useful alternative retention still needs its actual
large-profile symmetry/source join AND a quantitative interacting bound.
The complete coherent energy at `family_coherent_energy_retained_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:263`,
retains the signed debt; no expectation, variance or macro floor is
supplied by this test. MAIN remains the complete signed/direct retention input.

## MAIN mixed-test reconciliation (2026-10-09 20:10 UTC)

Read-only mathematical selection after `42a2b2e7`, not a new Lean proof or
kernel replay. ROOT inspected the cited source, with three independent bounded
screens. No new analytic field, source, action or normalizer was introduced.

The Fisher--Ward loop result does NOT silently extend to the actual AF
all-face source. `family_coherent_row`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:383`,
retains A_l=4*normSquared(aggregateCoherentTail_l), with the square of the
INCIDENT span, not the full family. `doubleIBPSource_amplitude_pin`,
`lean/YMGap/Continuum/QuaternionHaarPairedLinearDoubleIBP.lean:396`, has
ordered source 12*A_l-16*Gamma_l; it does not replace A_l by 4.
The latest loop `paddedSquare_original_own_variance_fisher_ward`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFisherWard.lean:205`, therefore
does not supply the same `48Z` correction for a coherent family.

A PAPER geometry diagnostic: for base>=2 take the spatial x0 link at
v=(0,1,1,0), with every other link equal to 1. Its four incident spatial
faces are p01 at v,v-e1 and p02 at v,v-e2. Their words are U,conj(U),U,conj(U).
With unit coefficients the incident span is 8*x0, aggregate tail is 4,
A_l=64 and Gamma_l=64*(1-x0*x0). At U=i the gradient square is 64;
the generic ordered source is 768-16*Gamma_l, not 48-16*Gamma_l.
This concrete incidence/evaluation specialization is NOT kernel-checked.
It is not an interacting-moment counterexample: it supplies no expectation
or concentration estimate under the original action. Constant coefficients
and vertex Gauss symmetry cannot alone pay a horizontal gradient square.
The existing exact Gauss declarations are `spatialSpan_gauss_zero` (:551)
and `blockConditionalRatio_gauss_zero` (:615) in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGaussTransfer.lean`.

The initially proposed extra ratio/ground-state reconstruction branch is
ALREADY supplied, at fixed parameters. `reciprocal_ratio_cleared_derivative`,
`lean/YMGap/Continuum/QuaternionHaarReciprocalRatioGradientBound.lean:104`,
retains the signed coupled derivative. `blockConditionalRatio_angular_reconstruction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalScore.lean:75`,
gives ell_V[(A^2*D(phi_(k+1))-(A*Db-b*DA))^2]<=epsilon at its COMPUTED
`blockAngularScoreCutoff` (:62). A=g_(n+t), b=T^t(g_n*psi), n+t>=1;
the clearing factor is A^2 and the weight is ORIGINAL V. No uniform bound
on its two cost inputs or on the changing-family onset is stated.
`energy_eq_bare_add_correction` (:144) and `endpoint_angular_cancellation`
(:173), `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean`,
also already retain the full endpoint correction and derivative cancellation.
Do NOT implement another derivative-convergence/ground-state wrapper.

The unpaid join is QUANTITATIVE, not this fixed-window approximation:
for a mixed Ward test h, sum_i (J_i f)(J_i h) is not Gamma(f), and its
original weighted pairing has not been bounded by the required transmitted
two-mass cost. `clearedRayleighCost`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131`,
is Z1*ell_V[b^2]-Z0*ell_V[b*Tb], with Z0=ell_V[A^2] and
Z1=ell_V[A*TA]. Neither is silently the local Ward variance's normalizer.
The positive incoming Ward-gradient pullback still contains T(Vbar*Ta),
NOT Ta or T^2a: `original_ratioNoise_gradientPayment_weighted_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:576`.
Likewise the exact coherent payment `family_coherent_energy_retained_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:263`,
retains its entire signed Taylor debt. No favorable sign is supplied by
per-face curvature, Gauss symmetry, positive Gram matrices or resolvent
upper bounds. A source/filtered-norm fraction relative to the RAW norm is
not imposed as a necessary condition; existing padded nondegeneracy is enough
for the selected shifted consumer's positive norm.

Decision: PRUNE copying `48Z` to coherent families and duplicating fixed-window
angular reconstruction. Retain the existing ORIGINAL signed-cost/noise
consumer `blockConditionalRatio_noiseCost_abs_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedPredictionPayment.lean:505`,
or DIRECT `PathShiftedWindowSurvival`,
`lean/YMGap/Continuum/BF4WilsonAllNomeShiftedWindowSurvival.lean:448`, for
`afPaddedZeroMomentumTrajectory`,
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:305`.
Neither changing-family quantitative producer is supplied by this screen.
No Lean edit/check, broad audit, new assumption, resource increase or chart
change; continuum/physical/QFT/every-group/Clay remain OPEN.

## Observed quantitative screens and the next joint payment (2026-10-08 UTC)

### Observed signed double-orbit join (2026-10-08 17:10 UTC)

The selected finite identity is now kernel-checked in the EXISTING leaf,
without another module, hypothesis bundle or changed frontier field:

- `lean/YMGap/Continuum/BF4WilsonAllNomePositiveOrbitResponseOrder.lean:696`,
  `signedOrbit_response_credit_identity`, proves the complete signed
  double-orbit identity below for every original completed x, arbitrary
  signed orbit list, rational theta and natural L,h. Repeated entries,
  empty lists, zero responses and negative E are not excluded.
- `:714`, `response_credit_nonnegative`, produces each late raw credit's
  sign for s>=1 from the existing cleared ratio order. Signed filter
  coefficients do NOT automatically preserve that sign after summation.
- `:730`, `response_credit_zero`, identifies the origin credit with
  the negative SAME early covariance, retaining its actual debit.
- `:740`, `smoothedResponse_credit_identity`, pins the calculation directly
  to the EXISTING `familyExcitation`, `timeKernel` and `smoothedResponse`.
  The trajectory source is already smoothed; no second averaging occurs.

The whole original signed right-hand side is now an exact mathematical
consumer of the existing covariance bounds and remaining late credits.
It does not have an automatically favorable sign. In particular no useful
changing-family lower credit or relative innovation ceiling is manufactured,
and no cleared factor is canceled without a produced positive floor.
For L=p=N/2 and h=N+1-p the target lag is N+1: b=R_x(N+2), or r_(h+1)
in warmed indices. No parity restriction is needed for this identity.

Independent Sol review read all 778 final-source lines and the actual
neighboring constructors, revalidated the hash, and found no mathematical
defect. Root inspected every addition and its actual source/response pins.
The decisive existing negative-E two-mode example is preserved. An auxiliary
exact-rational arithmetic screen confirms its identity, late signs and
positive margin; 3*Gamma_2 ALONE fails to pay that example. That arithmetic
screen is not a Yang--Mills instance, proof premise or additional Lean gate.

Verification: focused check 1 PASS, exit 0, with one 20-GiB capped compiler
and a 12-GiB reserve. The successful fresh preflight found no competing
Lean/Lake/pytest/runner process, 87% free memory and zero swap. Every new
printed helper/public gate (nine total) reports exactly
{propext, Quot.sound}. No limits were raised. No sorry, axiom, classical
input, native decision, witness erasure, broad/root/tree audit or baseline
refresh. Exact artifacts:

    /private/tmp/ym-oct8-signed-orbit-credit1.log
    SHA256 d6c7da56f63b6d0e6147b92fe3d01cfdad5b24cf6cdb8e7e7828a9dd314abe9a
    Final leaf SHA256 c003deeb026c595292ab6ab57e5e4401897cccd2406340a8f2421b7fe709aa97

CONTINUE: seek the actual COMPLETE original-family signed credit or the
existing relative-innovation producer, with OWN surviving variance, both
chronological masses and a justified physical family. Do not return to an
E>=0, local-floor sum, replica invariance or measured-mass shortcut. The
finite algebraic join is produced; original scaling control, independent
survival, physical mass/spacing, SAME continuum QFT, every group and Clay
remain OPEN. Canonical displayed claims unchanged; no chart reprint.

### Selected bounded experiment: retain the actual double-orbit credits

Inputs: the existing original completed response, `orbitSum`, its exact
double-response expansion, and `response_crossRatio` in
`BF4WilsonAllNomePositiveOrbitResponseOrder.lean`. For y=orbitSum(x,cs),
a=R_x(L+1), b=R_x(L+h+1), E=b-theta*a and
Gamma_s=a*R_x(L+s+h)-b*R_x(L+s), prove the cleared exact identity

    a*(R_y(L+h)-theta*R_y(L))
      = E*R_y(L) + sum_(j,k) c_j*c_k*Gamma_(j+k).

It holds even for signed weights, zero responses and negative E. For
s>=1, the existing ratio order produces Gamma_s>=0; Gamma_0=-Delta_h.
Consumer: the EXISTING smoothed-family/window-survival route, using the raw
family with `timeKernel`, not another smoothing of the trajectory state.
When p is the warm lag and N+1 the absolute target, h=N+1-p; the warmed
index h+1 must not be confused with absolute index N+2.
Prediction: a short exact finite join, with no new analytic field. The
zero-radius, zero-response and negative-E two-mode tests must remain valid.
Budget: one capped focused leaf and independent final-source review; no
root/tree audit. Revise if it duplicates the existing expansion, drops a
tail credit, requires E>=0, or cancels a response without a produced floor.
This experiment pays no original interacting scaling estimate by itself.

### Additional read-only route screens at HEAD `8e1aaedf`

The existing positive transmitted-response floor is NOT absent:
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:110`,
`family_time_geometric_floor`, gives rho^(2*t)*B(x,x) at each fixed
member. Its actual rho is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:165`,
`familyResponseFraction`, namely
w^12*(headFloor/prefixCap)^(56*F), F=family length. Using only the raw
variance floor in a transmitted-source entropy denominator would drop
this time-dependent factor. The existing conservative-band obstruction is
already proved in
`lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:64`,
`familyResponseFraction_le_ceiling`; do not build it again.
An entropy bound would additionally require an actual original local
exponential-moment producer. The gradient-payment pin is not an OWN-law
identification:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`,
`original_ratioNoise_gradientPayment_weighted_pin`, retains V*a*T(Vbar*Ta).
No transferred-response floor alone compares that weight with the OWN law.

The bounded-interference dual in
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDualFamily.lean:199`,
`family_norm_bound`, and `:376`, `family_partition_coercivity`, controls
ordinary original-action L2/coefficient coercivity, not temporal bond Gram
domination. PAPER false-join test: V=I and
B=[[r,-r+delta],[-r+delta,r]], with 0<delta<r<1/2, have 0<B<I and
individual response ratio r, but the source (1,1) has ratio delta. Sparse
interference plus individual floors does not repair signed-family control.
This is not a Yang--Mills counterexample. A joint ORIGINAL bond/OWN-variance
comparison remains a genuinely missing estimate, not a sum of local floors.

The fixed-carrier represented logarithm and domain-density joins are also
already present in `lean/YMGap/Continuum/BF4WilsonAllNomeBondOSLogarithm.lean:136`,
`representedLogarithmCertificate`, and
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSDerivative.lean:114`,
`densityCertificate`. Repeating their pairing supplies no changing-family
carrier, physical clock, continuum generator or QFT producer. A PAPER
pure temporal-prefix replica exchange leaves the squared initial source
difference fixed; it does not reduce the relative innovation without a
new source-weighted original seam estimate. No such estimate was produced.

Read-only mathematical/source selection at HEAD `6fe2e97f`, independently
screened by two Sol reviewers and checked against the cited source by root.
These are PAPER arguments and decisions, not new Lean theorems. The user's
`cf965d8e-085c-42c2-a303-16f0ae70d860/Pasted text.txt` attachment is already
reconciled in `RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`. Its useful
backward pin is the SAME physical source/transfer/time, not a numerical mass,
finite-spacing Kogut--Susskind identity, Sobolev sample convergence or an
area-law-to-gap theorem. Reuse that review; no duplicate literature scan.

### Direction test: curvature/Gram positivity is not an innovation ceiling

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalSignedGram.lean:114`,
`lastStep_local_signed_gram`, upper-bounds a score square by noise times its
Fisher payment. It does not upper-bound noise. The checked lower log-Hessian
in `lean/YMGap/Continuum/JacobiHeatNearFlatLogHessian.lean:142`,
`heat_logHessian_lower`, is for the weighted Jacobi heat on x>=0; it is not
the complete original conditional density or its surviving variance.
A PAPER 5/4 hemisphere curvature refinement still leaves the original-prefix,
antipodal and source-weighted payments. Do not build it merely to improve a
local constant without a useful innovation consumer.

The actual missing target remains
  Z*ell(blockNoise_d(a,phi_k)) <= epsilon_N*W*ell(b^2),
with a=g_(n+t), b=T^t(g_n*psi), phi_k the EXISTING reciprocal approximation,
Z=ell(a^2), W=ell((T^d*a)^2), and the literal OWN-centered source psi.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedPredictionPayment.lean:505`,
`blockConditionalRatio_noiseCost_abs_le`, already pays the difference from
the original transfer loss by eta+2*mixRate^k. This target, not an upper
bound on a different local score or marginal, is the quantitative consumer.

### Unsummed tilts: retain the signed response, then track its kinetic term

The existing two positive laws in
`lean/YMGap/Continuum/SU2QuaternionIntegratedScoreVariance.lean:79`,
`centeredSignedSquare_certificate`, imply more on PAPER than their average.
For I(d)=0, A=I(Q), b=I(Q*f), e=I(d*f), H=I(Q*f^2), J=I(d*f^2),
  det(C*Q +/- d,f) = C^2*(A*H-b^2)-e^2 +/- C*(A*J-2*b*e).
Each determinant is nonnegative when its corresponding positive-law
certificate is supplied. Averaging cancels the signed linear response;
it therefore cannot establish its favorable sign. For an affine full-density
perturbation Q_t=Q+t*d, Z_t*Var_t' equals
I[d*(f-mu_t)^2]-I(d)*Var_t. This derivative identity is PAPER, not a
constructed interpolation of the Yang--Mills action.

Here K=kineticWeight, V=spatialWeight and Vbar=spatialFringeMass. For the
ACTUAL incoming density Q=K*V*a, take the
cleared conditional residual X=A*phi-I(Q*phi). Its algebra gives
I(Q*X)=0 and I(Q*X^2)=A*noise. The latter is the existing private
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption.lean:96`,
`residual_square_pin`; the actual source-gradient absorption is
`original_ratioNoise_phiGradient_absorption_le:195` there. The full incoming
angular derivative d=J_in(Q) has zero head marginal by Haar IBP. The two
unsummed determinants consequently give on PAPER, PROVIDED both full-Q
positive-tilt certificates at the stated C are available,
  +/- C*A*I(d*X^2) <= C^2*A^2*noise-I(d*X)^2.
This display supplies neither a useful full-Q cap nor its scaling estimate.
All derivatives here are incoming; the outgoing A and conditional mean are
held fixed. Full IBP retains
  I(d*X^2)=Qdensity+Qkinetic=-2*A*M,
  I(d*X)=-A*I(Q*J_in(phi)),
where Qdensity=I[K*J_in(V*a)*X^2],
Qkinetic=I[(J_in(K))*V*a*X^2], and M=I[Q*X*J_in(phi)].
The retained negative square is a MEAN-derivative square, not M^2; it may
vanish without the mixed moment or gradient energy vanishing.

The actual Qdensity is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:74`,
`ratioNoiseDensityMoment`, not a zero-marginal total derivative. In
`original_ratioNoise_ward_unitGradient_le:337` there, writing R=Vbar^2*G^2
and P for the original positive gradient payment, the right-hand side is
  P-H[R*(J_out A)*Qdensity]-2*H[spatial].
Substitution gives the PAPER joint expression
  P+2*H[R*A*(J_out A)*M]
    +H[R*(J_out A)*Qkinetic]-2*H[spatial].
The kinetic and outgoing spatial responses have no produced favorable sign.
The exact `original_ratioNoise_gradientPayment_weighted_pin:384` uses the
incoming weight spatialWeight*a*T(spatialFringeMass*Ta), not the OWN-centering
law. Neither conditional centering nor the unsummed determinants identifies
its gradient payment with the required surviving variance.

DECISION: retain this joint signed expression and its negative square;
do NOT implement another tilt/interpolation certificate yet. Dropping the
square gives only an absolute relative-score cap, not a useful moving-family
payment. Even a fixed positive coefficient times (1-w) is insufficient for
an O(1/N) reserve on the selected AF family: the checked
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:376`,
`afGap_side_gt_at_probe`, makes N*(1-w) cofinally unbounded. This screens
the cap-based argument, not the actual interacting innovation or survival.

### Source selection remains flexible, but mean cancellation is not energy control

`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:151`,
`familyExcitation_norm_floor`, and `familyExcitation_correlator_pin:187`
already admit explicit signed profiles with physical/Nodup guards and
positive sum(c_p^2). No extra source constructor is needed. Yet EVERY
physical profile, including zero-sum coefficients, retains Casimir 12 by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCasimir.lean:294`,
`spatialSpan_casimir`. The actual normalized raw energy is
  12*(1-w)*OWN_variance+varianceRemainder,
by `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`,
`padded_family_energy_variance`; its remainder retains BOTH Taylor debts
and the full density response. This raw identity is not a Casimir pin for
the filtered conditional ratio.

The explicit antisymmetric profile already removes its OWN/Gram means,
but `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:248`,
`original_energy_response_budget`, still requires the actual even source-jump
cost and signed cross credit. The full adjacent identity in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentFullAngular.lean:451`,
`adjacent_full_angular_paid`, retains the six nonshared-link
contributions and transported-loop deficit. Vertical Gauss zero or a
coefficient incidence identity does not remove those horizontal quantities.
This does NOT prune action-dependent signed cancellation or spatial profiles;
it prunes another mean-zero/profile interface as a substitute for the estimate.

### Continue/revise test

NEXT is an ORIGINAL complete signed moving-window estimate or useful relative
innovation, with BOTH chronological masses and OWN surviving variance. For
the Ward alternative, compare the kinetic/spatial/mixed contributions JOINTLY;
do not require separate small absolute bounds. The one-plane expression
above alone is not the multi-plane, multi-step block estimate. Keep the
direct box-survival route co-primary, including its nonnegative tail credits;
a useful raw near-unit ratio is sufficient, not a mandatory prerequisite.
Source-profile changes need their actual family pins, not measured overlap.

Decisive tests before implementation: zero/constant sources, constant terminal
input with nonzero J(V), full incoming versus frozen jets, antipodal region,
changing OWN centers, and w->1 with N*(1-w) unbounded. Abandon/revise if the
proposed estimate only relocates one signed term, uses the wrong gradient
weight, reverses a Gram inequality, or pays a global absolute score cap.
This checkpoint launches ZERO Lean checks and adds no Lean file, hypothesis,
axiom, frontier field or proof-status change. Continuum survival, calibration,
limiting OS/QFT, every group and Clay remain OPEN; no ASCII reprint.

## Selected finite physical-source Gauss join (2026-10-08 UTC)

OBSERVED (2026-10-08 16:30 UTC): the selected finite join is now CHECKED.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGaussTransfer.lean:551`,
`spatialSpan_gauss_zero`, retains physical membership of every signed or
repeated face; `shifted_gauss_zero:566` uses the EXISTING shifted polynomial
and any literal rational center, including the chronological OWN center.
`iterateStep_gauss_zero:575` respects the actual tail recursion;
`terminalMessage_gauss_zero:585` is about literal T^n(1), not stationarity.
`blockConditionalRatio_gauss_zero:615` preserves the actual g_(n+t),
T^t(g_n*psi), existing upper window and every finite reciprocal degree.
Source/message algebra admits arbitrary nome/K and zero width; the ratio
keeps its existing strict-nome/head-cutoff positivity guards. This supplies
the finite physical-source constraint input, not a horizontal estimate.

Final focused check 2 exits zero in 3.71 seconds; ALL ten printed gates
stay within {propext,Quot.sound}, and all five new gates use exactly those
two permitted axioms. Source: 643 lines (+221), SHA256
  39a7a8f1bd137e13eb088d5b9bcf57f6aa8e0c2e1686d350c294d273393b80a9.
Log `/private/tmp/ym-oct8-physical-source-gauss2.log`, SHA256
  1be8693cc0e7effa577b1e233445bec18aaf53826dd90afffb6dc0fb62dca1f4.
Two unchanged lint warnings and one unused recursion binder are reported,
not suppressed. Check 1 fails on missing namespace names and unfolding
timeouts; its error-recovery sorryAx output is NOT proof evidence.
Repairs only resolve names and shield existing bulky definitions locally;
no theorem statement, analytic premise or resource option changes.

Both launches followed successful fresh process/memory preflight: no
competing compiler/runner/test process, 84--86% memory-pressure headroom,
zero swap, one 20-GiB worker and a 12-GiB reserve. No limit raise, lock
bypass, user-process termination, new module/frontier/sorry/axiom or root/
tree build/audit; existing root import unchanged, CI still manual-only.
Root read the complete source plus repair and complete final log.
Independent COMPLETE final-source review PASS at the same 643-line source
hash: raw physical placement, supported Haar reflection, signed/OWN
centering, actual iteration chronology and reciprocal degree all retained.
CONTINUE with the actual complete signed moving-window payment or relative
innovation. Do not impose an extra ambient charged-field Gauss domain on
the existing closed-loop algebra. Physical/continuum/QFT/every-group/Clay
remain OPEN; exact canonical displayed claims are unchanged.

The supplied lattice-measurement attachment is already reconciled in
`RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`; no measured mass,
finite-spacing Kogut--Susskind identity, Sobolev sample regularity or
area-law-to-gap premise is added. Its useful backward requirement is the
SAME physical, gauge-invariant source and transfer, not a numerical gap input.

Selected proposition in the EXISTING `BF4ExactSlabFixedSpatialGaussTransfer`
leaf: the literal slice generator annihilates every physical signed
`spatialSpan`, every original terminal message, and every original finite
`blockConditionalRatio` of a supported Gauss-invariant input. Subtracting
the literal OWN rational center must preserve that statement. Available
inputs are `SliceHeat.plaquette_pin`, actual closed-character endpoint
cancellation, supported Haar reflection, `transferStep_gauss_zero`, the
actual `DirichletWindow.terminalMessage_next`, and finite reciprocal algebra.
All spatial face memberships are required: polynomial support alone does
not imply that the source word closes. No padded equality is differentiated.

Consumer: finite physical-source admissibility for the existing original
conditional prediction/score construction, a necessary QFT-side input.
Prediction: finite algebra and induction suffice without any new analytic
hypothesis. Tests: signed/repeated faces, empty lists, zero width/cutoff,
arbitrary terminal depth and reciprocal degree, support/fringe and OWN
centering. Completed generator domains and gauge-group exponentiation are
NOT inferred. This does not pay a horizontal derivative or scaling estimate.

Budget: one existing Lean leaf, at most 400 added lines and four focused
checks, each serialized after fresh process/memory preflight with one
20-GiB worker and a 12-GiB reserve. Sol implements; independent read-only
review inspects the complete final source. Abandon/revise if closure needs
an assumed gauge law, a different action/carrier, differentiated padding,
unjustified reciprocal denominator or an unbounded completion extension.

Parallel MAIN selection: the coherent-energy and weighted-Casimir screens
retain the full original density and BOTH signed Taylor debts, but produce
no changing-family relative upper bound. Casimir of the raw spatial family
does not identify the filtered conditional ratio's Casimir. Opposite
incidence alone does not annihilate the coherent tail. Prune another local
cancellation/IBP wrapper; preserve complete signed window payment or
relative innovation as the main analytic frontier. No canonical chart
claim changes from this selection.

### Observed MAIN analytic screen: no free incidence/Casimir payment

`BF4ExactSlabFixedSpatialFamilyCoherentTail.family_coherent_row:383`
retains the squared SUM of signed tails and its negative incident-span square.
`BF4ExactSlabFixedSpatialAdjacentAngularCancellation.original_adjacent_angular_difference:203`
retains the transported difference character, not a coefficient-difference
bound. Its actual odd-marginal consequence is `original_adjacent_marginal_angular_le:249`.
`BF4ExactSlabFixedSpatialFamilyRelativeWard.padded_family_energy_relative_ward:333`
still has the explicit factor 24+24*|qs|*marginalScoreCap(w)^2 and the
COMPLETE signed normalized remainder. These are existing theorems, not new
proof progress. The actual unit family has |qs|=3*N^6 at base=N^2.

The alternative weighted-Casimir calculation is PAPER only. For raw
f=spatialSpan and phi=f-c, IBP gives
  H[W*Gamma(phi)] = 12*H[W*phi^2]+12*c*H[W*phi]
                    +(1/2)*H[phi^2*Delta(W)].
The density-Laplacian is unpaid. In particular, the actual payment density
from `BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.original_ratioNoise_gradientPayment_weighted_pin:384`
contains spatialWeight*a*T(spatialFringeMass*Ta), not the OWN-centering law;
its mean term need not vanish. No Casimir-12 pin for the filtered ratio is
produced. PRUNE another IBP wrapper; keep the complete signed payment in
the SAME surviving variance units as the analytic obligation. This screen
does not refute a favorable interacting cancellation or actual survival.

### Backward domain screen: prune an extra ambient Gauss prerequisite

The ACTUAL dense syntax already consists of closed physical loops:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonProbe.lean:45`,
`SourceLoop`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindow.lean:50`,
`WindowExpression`; and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonIntrinsicForm.lean:45`,
`IntrinsicExpression`. The existing
`lean/YMGap/Continuum/BF4ExactSlabVertexGaussClosedCharacter.lean:579`,
`placedWindow_gauss_zero`, annihilates each placed dense test with BOTH
placement-room guards. These source facts are prior proofs, not new closure.

The physical pairing is pinned by
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:63`, `bondForm`;
its SAME completed carrier by `dense_limit:190` there and
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSCompletion.lean:365`,
`constant_pairing`. Do not impose an unbounded Gauss generator on a LARGER
charged-field algebra as an extra prerequisite for these closed observables.
No such generator or domain extension is constructed, and no canonical
field is changed or discharged by this planning decision.

For a larger algebra, the radical/closability argument remains PAPER and
requires a G-stable dense domain (including G^2*p), SAME-form antisymmetry
and fixed-test continuity/density. Full-action Ward and transfer
intertwining alone do not supply that realization or a reflected
two-endpoint antisymmetry pin. PRUNE that extra branch for the present
physical test algebra; keep the actual conditional-source constraint join.

## Observed late-response saturation (2026-10-08 16:11 UTC)

CHECKED in the existing leaves, with no new module or conditional compiler:

- `lean/YMGap/Continuum/BF4WilsonAllNomePositiveOrbitResponseOrder.lean:448`,
  `response_crossRatio_increment_le_late_defect`, proves
  Delta_h<=(r_0-r_1)*r_h on the SAME original completion. Every natural
  shift and h, including odd shifts, zero responses and h=0, is retained.
  The remainder is r_0*(r_h-r_(h+1))>=0. Unlike the earlier h*S bound,
  no positive rational response floor is required.
- `lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:240`,
  `saturationDiagnostic_rates`, checks 0<1/5<99/100<1.
  `saturationDiagnostic_payment:248` checks the literal N=2, p=1, h=2,
  theta=37/40 box and the STRICT chain
    Delta_2 = 73525221/500000000
      < (r_0-r_1)*r_2 = 1662130001/10000000000
      < E*Total = 168190595904875349/1000000000000000000
      < 2*S = 617859/2500000,
  with E>0 and actual box survival. These are abstract positive-mode
  moments R(k)=(1/5)^k+(99/100)^k, NOT a Wilson/Yang--Mills instance.
  `saturationDiagnostic_negativeCredit_survival:263` additionally checks
  that the SAME box survives at theta=189/200 while E=-179849/100000000<0.
  All three new diagnostic gates are AXIOM-FREE kernel `decide` proofs.

### Decision: bound the cost without imposing an unnecessarily strong test

The original h*S theorem remains correct and useful as a fallback; it is
not a necessary survival condition or the primary required family estimate.
The late-response bound materially improves that fallback in the checked
diagnostic without replacing the action, carrier or normalization.
Neither sufficient bound supplies actual changing-family credit.

Independent PAPER review also retains the previously dropped tail credits:
for a=r_1, b=r_(h+1), C=r_0, E=b-theta*a and
Gamma_s=a*r_(s+h)-b*r_s>=0 (s>=1), exact double-box expansion gives
  a*(N+1)^2*[R_Y(N+1)-theta*R_Y(p)]
    = E*(C+Tail)-Delta_h+sum_(s=1..2*N) tau_s*Gamma_s.
The Gamma signs follow from existing `response_crossRatio:263` in the
positive-orbit leaf; this exact triangular-recoding join remains PAPER,
not a new Lean window certificate. The negative-E diagnostic explains why
discarding those credits can exclude valid survival. Preserve signed
credit and residual damping; do not impose E>=0, uniform E>=gamma*C,
or h*S payment as a mandatory frontier. In this expansion x is the RAW
centered family and Y its existing box average, not another average of
the already smoothed trajectory state.

The concrete original-action residue is still unproduced. The finite
`BF4DyadicWilsonSquareFilteredGainStein.paddedSquare_own_commutatorGain_source_gradient`
at `lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainStein.lean:190`
retains the full V*g_n derivative and OWN-center correction; it is not a
favorable estimate on the warmed signed spatial family. The actual
`normalizedFiniteGain_identity` at
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredFiniteGainApproximation.lean:87`
and `normalizedFiniteGain_approx` at
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredFiniteGainLimit.lean:111`
retain chronological normalization and only identify/approximate the
fixed-member gain. Gauge-vertical Ward zero and the integrated angular-score
variance certificate do not produce a horizontal temporal-residual upper
bound. Do not build another join identity in place of that missing estimate.
Continue actual complete signed window/cost-versus-variance control or the
existing relative innovation, with these bounds as optional upper payments.

### Exact verification boundary

Actual bound final source (651 lines), SHA256
  8dcc1509a2cd8362921b7d3af3c2838facf94df08a738f3b1b2e486b3783f193;
focused check 2 `/private/tmp/ym-oct8-late-defect2.log`, SHA256
  f54bebff362511b6ae7a55d729f0e63b9e566b9b5053010f7fe65880798d80f8.
Diagnostic final source (288 lines), SHA256
  c4a4e5072eb4ec865328835769e4c003abaae80d3cc2012f541aa7864f89ff10;
focused check 1 `/private/tmp/ym-oct8-saturation-diagnostic1.log`, SHA256
  cf38671e7cfa5783d92feb76a3ef4dca2ab899e4f7bfe415966d30e6438f1f1f.
Both checks exit zero with no warnings/errors/sorryAx; all existing printed
gates permitted, new actual-bound gate exactly {propext,Quot.sound}.
Independent COMPLETE final-source review PASS at both hashes; root read
both complete sources, the final repair and complete logs. Actual check 1
rejected only binder V shadowing local notation; alpha-renaming U,V to U0,V0
fixes it. Its error-recovery sorryAx is NOT accepted proof evidence.

Exactly +32 actual-bound and +46 diagnostic lines, three focused attempts
within budget. Every launch followed successful fresh process/memory
preflight, one worker, 20-GiB hard cap and 12-GiB reserve; memory-pressure
headroom 85--86%, swap zero. A sandbox-denied initial swap query prevented
launch; read-only authorized preflight then succeeded. No lock bypass,
user-process termination or threshold increase. No root/tree audit, baseline
refresh, new sorry/axiom, frontier field change or broad verification claim.
Continuum survival, physical calibration, SAME limiting OS/QFT, every group
and Clay remain OPEN. Canonical displayed claims unchanged; no ASCII reprint.

## Selected late-response saturation (2026-10-08 UTC)

Previous goal turn PROGRESS: 7ee63221 checks Delta_h<=h*S, with explicit
original-norm warming. Fresh source review confirms that the useful actual
changing-family payment is still missing. Independent mathematical tests now
show that h*S can overcharge even positive first-split credits, so it is a
fallback, not a mandatory or primary analytic frontier.

Selected unconditional proposition in the EXISTING positive-orbit leaf:
  Delta_h <= (r_0-r_1)*r_h,
with r_i=B(x,T^(L+i)x). The exact gap is
  (r_0-r_1)*r_h-Delta_h = r_0*(r_h-r_(h+1)) >= 0.
Available inputs are the SAME response positivity, first-defect positivity
and quotient algebra; no rational response floor, norm inverse or spectral
measure is required. This retains actual late decay rather than h growth.
Consumer remains the PAPER first-split box payment for
`BF4WilsonAllNomeShiftedWindowSurvival.PathShiftedWindowSurvival` (line 448).
For that box calculation x is the RAW centered family; the trajectory state
is already the smoothed Y and must not be smoothed twice.

Prediction/decisive test: all shifts, h=0, zero norm and zero spread remain;
the two strict rational modes 1/5 and 99/100, N=2, p=1, h=2,
theta=37/40 give Delta_2 < (r_0-r_1)*r_2 < E*Total < 2*S, E>0.
Implement an exact kernel-decided certificate in the EXISTING rational
two-mode diagnostic leaf. This is NOT a Wilson state or a Yang--Mills
counterexample; it tests the sufficient payment's overcharge, not survival
of the actual changing family. No conditional compiler or new bundle.

Budget: <=55 lines for the actual bound, <=70 for the diagnostic;
<=3 root-owned focused checks, one 20-GiB worker and 12-GiB reserve with
successful fresh dynamic process/memory preflight before EACH launch.
Sol implementation and independent full final-source review; root inspects
complete source and gates. Revise/prune if the claimed upper gap has the
wrong sign or either diagnostic comparison fails. No resource-option
increase or field change. Continue the ORIGINAL joint window credit or
relative innovation; the actual horizontal/Stein residual estimate remains
unproduced. Gauge-vertical Ward zero does not pay its temporal norm.

## Observed temporal covariance payment (2026-10-08 15:58 UTC)

CHECKED in the EXISTING positive-orbit response leaf, not another survival
compiler or frontier bundle:

- `lean/YMGap/Continuum/BF4WilsonAllNomePositiveOrbitResponseOrder.lean:406`,
  `response_crossRatio_increment_le`, proves Delta_h<=h*S for
  r_i=B(x,T^(L+i)x), S=r_0*r_2-r_1^2 and
  Delta_h=r_0*r_(h+1)-r_1*r_h. Every nonnegative integer shift L, including odd L,
  is retained. The actual supplied rational floor for r_0 is used ONLY
  for order reflection, with no numerical loss in the bound.
- `:458`, `warmed_response_crossRatio_increment_le`, produces
  Delta_h<=h/(q+1)^2 * R_x(2q)*B(x,x). Both factors are the SAME original
  completed source; q is the number of warming steps, not the moment shift.
  This is an upper covariance bound in the ORIGINAL preimage norm,
  not a relative spread or survival estimate.

### Mathematical contraction and actual consumer

The selected proof was generalized to arbitrary shifts without a half-time
state. Construct CReal coefficients and their Type-level QCauchy data from
the ACTUAL pairing representatives, using quotient induction on x; there is
no chosen representative or extraction from CReal's propositional Cauchy field.
For y=r_0*Tx-r_1*x the exact shifted residual satisfies
  B(y,T^L y)=r_0*S,
  r_0*Delta_(h+1)=r_1*Delta_h+B(y,T^(L+h)y).
Residual response monotonicity, 0<=r_1<=r_0 and S>=0 pay the recurrence
by induction. The warming corollary retains the favorable square through
  r_0*d_2-S=d_1^2,
then composes the existing actual two-defect bound. It does not identify
an ordinary weighted marginal or finite chronological Gram with the
completed reflected form.

The box-window join below remains PAPER, as in the earlier direct-window
section; no kernel-checked triangular-recoding or window certificate is
claimed here. At its first split let a=r_1, c=r_h, b=r_(h+1),
E=b-theta*a, C=r_0. The exact retained payment is
  a*(c-theta*C)+E*Tail = E*(C+Tail)-Delta_h.
The new checked estimate reduces a sufficient payment to
  h*S <= E*(C+Tail).
This JOINT actual-source inequality remains UNPRODUCED. Preserve its signs;
do not impose a uniform E>=gamma*C or polynomial original-to-warmed overlap
as a new mandatory frontier. Uniform positive gamma would already give raw
retention at h+1, hence h, and the existing positive-orbit retention theorem
would consume it directly. The preimage-norm bound offers another sufficient
route, not a necessary overlap condition.

For the actual dyadic window j>=2, L=p=N/2, q=N/4 and h=N/2+1;
the proved coefficient specializes on PAPER to 8*(N+2)/(N+4)^2.
Do not use q=p or invent T^(1/2) at j=1; the core theorem already covers
that odd shift, while its warming corollary names only the even shift 2q.
Source-specific relative S/late credit is still absent. Existing
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredGainLimit.lean:131`,
`gainLimit_completed_pin`, is an identity, not an upper producer;
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredGainSourcePair.lean:155`,
`commutatorGain_source_pair`, still retains the full action and OWN-center
residue. No stationary, free, heat-bath or different-group carrier is used.

### Exact verification boundary and decision

Final focused check 2 exits zero, no warnings/errors/sorryAx. Both new public
gates and the existing printed gates stay within {propext, Quot.sound}.
Final source SHA256:
  7fa07b290672faaa526304860d201323aea11532532ea3e71e0e0b21acb3a823
Log: `/private/tmp/ym-oct8-temporal-covariance2.log`, SHA256:
  b1cede9527af8c813dc0bed71c2283fb7ba51c8cd1438388f76f7a92f0e1c523
Root inspected the complete final source; independent complete final-source
review PASS on that exact hash. Check 1 rejected a zero-case rewrite leaving
one L+0 occurrence; simplification of BOTH occurrences fixes it. Its printed
sorryAx was error recovery, not accepted proof evidence or committed code.

Each actual launch followed successful fresh process/memory preflight and
used one worker, hard 20 GiB, reserve 12 GiB; pressure-free memory 86%, swap
zero. Initial process queries matched their own shell through an unbracketed
name; NO compiler was launched until corrected queries were empty. No user
process killed, threshold raised or lock bypassed. No root/tree audit,
baseline refresh, new module, sorry/axiom or canonical field change.

CONTINUE the actual JOINT credit/spread or last-window innovation estimate.
The long-lag covariance now has a proved three-moment upper payment, but
its useful changing-family size and the PAPER box join remain open. The
measurement attachment supplies neither. Scaling, physical mass, SAME
limiting OS/QFT, every group and Clay remain OPEN; displayed canonical
claims unchanged, so no ASCII reprint.

## Selected temporal covariance payment (2026-10-08 UTC)

Exact next proposition on the SAME completed original Wilson carrier:
for r_i=B(z,T^i z), S=r_0*r_2-r_1^2 and
Delta_h=r_0*r_(h+1)-r_1*r_h, prove Delta_h<=h*S whenever
the already constructed positive rational norm floor is supplied. This is
an upper estimate, not another conditional window-survival compiler.
Consumer: the retained early-credit test for
`BF4WilsonAllNomeShiftedWindowSurvival.PathShiftedWindowSurvival` at line 448.
At the first split its exact signed payment is
  (b-theta*a)*(r_0+Tail)-Delta_h,
not the conservative discarded-credit payment theta*a*r_0.
Thus the new estimate reduces a long-lag covariance to the SAME three
initial warmed moments. The actual favorable late credit and relative
spread/overlap estimate remain unsupplied.

Available inputs inspected by root: original real-scalar action and its
explicit Cauchy witnesses (`BF4WilsonAllNomeCompletedRealScalar` and
`CRealSeminormPairingCompletionLimit.representativeInnerCauchy`), positive
time contraction (`BF4WilsonAllNomeTimeDefectMoments.completedTime_form_le`),
actual Cauchy--Schwarz, lag balance and the existing rational-floor order
cancellation. No spectral measure, normalized Rayleigh quotient or inverse
is required. Use the unnormalized residual y=r_0*Tz-r_1*z:
  B(y,y)=r_0*S,
  r_0*Delta_(h+1)=r_1*Delta_h+B(y,T^h y).
Induction and 0<=r_1<=r_0 pay this by r_0*(h+1)*S; cancel only the
already supplied positive floor. Independent mathematical review is pending.

Also compose the ACTUAL warming estimate before interpreting its size.
For the window r_i=R_x(p+i), p=N/2 and h=p+1. At j>=2 warm by
q=p/2=N/4, NOT by p; then z=T^q x and r_i=R_x(2q+i).
`BF4WilsonAllNomeTimeDefectTail.mixedMoment_two_defect_bound` (line 100)
pays d_2 by m_0/(q+1)^2, m_0=B(x,x), hence on PAPER
  h*S <= 8*(N+2)/(N+4)^2 * r_0*m_0.
The earlier independent screen's doubled-time mismatch was caught and
corrected before code. This is O(1/N) in the ORIGINAL preimage norm,
not useful relative control in r_0^2 without an actual overlap estimate.
For j=1, do not invent a half-time state; keep shifted mixed moments or
handle that finite stage separately. No canonical field is weakened.

Prediction/test: cleared recurrence, h=0 and h=1 must agree exactly;
one-mode spread is zero, two-mode spread need not be relatively small.
The positive floor belongs to the supplied state, not a universal scalar.
Verification budget: extend the existing positive-orbit response leaf,
one serialized 20-GiB worker and 12-GiB reserve, fresh successful dynamic
preflight before EACH launch; at most three focused attempts before
reassessing. No root/tree audit, new frontier or classical gate. Sol
implementation, independent read-only review, root complete final-source
inspection. Revise if real-scalar data or original-time identities cannot
be constructed; abandon any replacement by a stationary/free carrier.

## Observed geometric cap/floor obstruction (2026-10-08 UTC)

CHECKED in the EXISTING AF trajectory leaf:
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:608`,
`afGeometricCertificateProbeScale`, returns a computable cofinal probe;
`afGeometricCertificateProbeScale_ge_start:611` retains any supplied start.
`afGeometricCertificate_lt_at_probe:618` proves rho^(N/2+1)<theta for
EVERY 0<=rho<=1 with afGap(j)<=1-rho at that probe.
`afGeometricCertificate_no_eventual_floor:668` excludes an eventual fixed
positive scalar floor even for a scale-dependent rho. The proof uses the
actual rational AF denominator and reciprocal Bernoulli, not asymptotics.
The probes are >=1, where the dyadic side is even and the displayed exponent
is the ACTUAL backward lag. Endpoints rho=0,1, theta>1 and nonreduced positive
rationals are retained. Neither a Wilson response ceiling nor an interacting
energy lower bound is asserted.

Observed verification: focused check 2 exits zero, no warnings/errors.
The probe is axiom-free; the other three new public gates are exactly
{propext,Quot.sound}. All existing printed gates remain permitted, with no
sorryAx. Check 1 rejected only the corollary's reversed order composition;
root repaired it to theta<=power<theta. Its error-generated sorryAx is NOT
accepted proof evidence. No new source sorry, axiom, option, import or frontier.
Exactly 121 lines added (final 721), within the 160-line/two-check budget.
Root read the complete source and the exact final repair; independent
complete-source mathematical review reconciled to the final hash PASS.
Only this leaf and its olean were checked; no root/tree build, audit, guard
or progress metric. One monitored 20-GiB worker, 12-GiB reserve; memory
preflights 87% then 86% pressure-free, zero swap. Process preflight passed
before check 1. The second refresh's awk matcher FAILED; it was corrected
immediately, finding no competing compiler/test/runner after the brief check.
This is a procedural preflight defect, not a fully passing second preflight;
future launches must stop if ANY preflight command fails, before compiling.

```text
SOURCE lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean
SHA256 94cd6132b4245a558476f4665bb4e89987372e4dae24252e0895a6c90dd8f1b5
CHECK  /private/tmp/ym-oct8-af-geometric-certificate2.log
SHA256 fc045df278600bbc0a13fa9f8302cbf1d38481da9e8bc6eae86e5ed7c0703fc3
```

Decision: PRUNE the proposed geometric rescue of the coarse cap/floor
certificate, whose PAPER loss >=48*afGap meets the stronger checked screen
already at loss >=afGap. The algebra linking the original energy cap and
variance cap to 48 remains the earlier PAPER strategy diagnostic, not a new
formal energy bound. This result does NOT refute actual smoothed survival,
the later-moment credit/payment test, or the Yang--Mills theory. Continue
MAIN with the SAME-source signed moving-window credit/payment or original
relative-innovation estimate, not another propagation compiler. Physical
scaling/calibration, QFT, every group and Clay stay OPEN. No canonical field
or exact displayed claim changes, so no chart reprint.

## Selected geometric cap/floor obstruction (2026-10-08 UTC)

Exact proposition: for each positive rational theta and supplied start,
construct j>=start such that EVERY scalar 0<=rho<=1 with
afGap(j)<=1-rho satisfies rho^(side(j)/2+1)<theta. This is a necessity
for a proposed sufficient GEOMETRIC certificate, not an upper bound on an
interacting response. The consumer being screened is
`BF4WilsonAllNomeOddResponseJensen.response_shift_floor`, against the actual
backward lag of `BF4WilsonAllNomeShiftedWindowSurvival.PathShiftedWindowSurvival`.
It removes the proposed rescue of the coarse cap/floor strategy by replacing
its nonpositive linear Bernoulli credit with geometric propagation. It does
not remove or change a canonical analytic field.

Available inputs: the existing explicit cofinal `afBareHeatProbeScale` and
`afGap_side_gt_at_probe` in `BF4WilsonAllNomeAFPaddedTrajectory`, and
`ReciprocalBernoulliUpper.oneSub_pow_mul_bernDen_le`. At h=N/2+1, N<=2h.
Use the explicit cap 2*ofNat(theta.den): theta*ofNat(theta.den)>=1, while
reciprocal Bernoulli and theta<=rho^h would force theta*N*afGap<=2,
contradicting the probe. No logarithm, limiting argument, inverse, spectral
measure, physical-spacing assumption or actual-transfer identification.

Predicted result: the scalar geometric certificate cannot stay uniformly
positive on this schedule even with loss merely >=afGap; the cap/floor
strategy's PAPER loss >=48*afGap is therefore not rescued. Test rho=0,
rho=1, theta>1, j=0 and arbitrary supplied start. No lower bound on the
actual interacting energy or failure of actual smoothed survival follows.
Implement in the EXISTING AF trajectory leaf, no new module/interface.
Budget: <=160 added Lean lines, <=2 root-owned focused checks, one worker,
20-GiB ceiling and 12-GiB reserve with fresh dynamic preflight at each launch.
Independent final-source mathematical review is required. Stop/revise if
the only result duplicates the bare w^(12*N) obstruction or needs a new
analytic premise. Main signed moving-moment credit/payment and original
relative innovation stay OPEN and primary. No chart reprint.

## Observed SAME-slice Gauss/ORIGINAL-transfer join (2026-10-08 UTC)

The selected finite join is now CHECKED, not an assumed invariance interface.
`lean/YMGap/Continuum/SU2QuaternionHaarBlockEmbeddingAngular.lean:116`,
`BlockEmbedding.polynomial_ratDerivative_exact`, transports the actual raw
partial derivative through an injective block placement. Its
`polynomial_blockAngularDerivative:136`, `ratDerivative_offImage_zero:159`,
`blockAngularDerivative_offImage_zero:192` and
`polynomial_supportedHaar_reflect:207` retain support/sentinel guards and
reflect equality on the SAME supported source. No padded identity is
differentiated.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGaussTransfer.lean:50`,
`sliceGauss`, sums the actual minus-left outgoing/plus-right incoming
generator on every literal baseLinks entry, including fringe. Its
`sliceGauss_supported:98` preserves the source. Per-face original action
invariance, the full spatialIds product and supported Haar reflection produce
`spatialWeight_gauss_zero:281`; zero of a subset is NOT inferred from zero
of the full action. `transferStep_gauss_intertwining:391` proves G(Tp)=T(Gp)
at arbitrary-insertion Haar strength for every supported signed p, with
T=P(V*p) the ORIGINAL transfer and V the full spatial weight.
`transferStep_gauss_zero:406` preserves an actual supplied Gauss-zero source.
Arbitrary nome, K=0 and width zero remain; no positivity, stationary vacuum,
gauge fixing, inverse or omitted action factor is used.

Root inspected complete final sources and all repaired joins. Independent
COMPLETE FINAL-source mathematical review PASS at the hashes below. Accepted
focused core check 2 and instance check 3 exit zero: SIX core gates exactly
{propext,Quot.sound}; the instance definition uses only propext and FOUR theorem
gates exactly {propext,Quot.sound}. The instance has two harmless lint warnings
(unused private support parameter; simpa instead of simp). Rejected logs are
not proof evidence; their synthetic sorryAx/failed constants are not accepted
axioms or source holes. The recorded single revision to five checks total
was exhausted, not exceeded. Final sources are 228+422=650 lines. No resource
option increase, new hole/axiom/classical input, tree build/audit, guard or
progress metric. Every launch had fresh approved process/memory/swap
preflight, one 20-GiB-capped worker and 12-GiB reserve; final memory-free
reading 87%, zero swap. Root imports are registered ONLY.

```text
SOURCE lean/YMGap/Continuum/SU2QuaternionHaarBlockEmbeddingAngular.lean
SHA256 ee71adb14ac0e68485ec1786c582ea1a106c93cafe8ca8d9a46e133f7ee9cb11
CHECK  /private/tmp/ym-oct8-block-embedding-angular2.log
SHA256 a4d0ed06848e13f1900b5a2506c12ba5dc355b5a5fa1ac13fce83743543d502e
SOURCE lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGaussTransfer.lean
SHA256 ab5c613eb5aadfb9123415b9fa4de3a146e324238395983460106167b474ce5b
CHECK  /private/tmp/ym-oct8-slice-gauss-transfer3.log
SHA256 caba608c6e34300c5ef1814d312494bdcf2eca882905562909654e53261ddad1
```

Decision: close the selected FINITE gauge/transfer join; do not extend its
generator to every completed state without an actual domain/control theorem.
Return MAIN work to the changing-family signed moving-moment credit/payment
or original relative-innovation ceiling. Collective gauge cancellation does
not pay horizontal energy. The attachment's mass/spectral-limit distinctions
remain incorporated in the calibration audit; no measurement-driven premise
is added. Completed/continuum gauge transport, survival, physical mass, full
QFT, every group and Clay remain OPEN. Canonical displayed claims are
unchanged; no chart reprint.

## Selected independent finite Gauss/transfer join (2026-10-08 UTC)

The measurement attachment is already incorporated in the calibration audit;
no measured mass, Sobolev regularity or finite-spacing Hamiltonian identity is
adopted as a proof premise. Three bounded read-only reviews found no producer
of the useful moving-window credit or original relative-innovation ceiling.
In particular the existing cap/floor strategy requires epsilon>=48*(1-w):
`FamilyKineticUpper.family_energy_nome_normalized` has cap 192*(1-w)*C,
whereas `FamilyRayleighFloor.family_oddVariance_coefficient_cap` gives the
matching OWN variance <=4*C. This obstructs THAT certification strategy,
not the actual energy. The joint density/Hessian IBP square still leaves
the actual weighted ratio-Hessian energy unpaid. Do not build another
propagation or curvature rearrangement as if either estimate were produced.

Root source reconciliation makes that cap diagnostic sharper on the ACTUAL
rational AF schedule, still a PAPER deduction: with C>0, the cap/floor test
forces N*epsilon>=4 at EVERY index, since
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:462`,
`af_squareLinearHeatBudget_ge_one`, already proves 12*N*(1-w)>=1.
Thus its elementary 1-N*epsilon retained-fraction estimate is nonpositive;
no asymptotic guess or new parameter sweep is needed. The cap is the literal
2*normalizedEnergy<=384*(1-w)*C at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyKineticUpper.lean:266`,
`family_energy_nome_normalized`; the variance cap is at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyRayleighFloor.lean:104`,
`family_oddVariance_coefficient_cap`. No lower bound on the actual energy,
failure of the weaker moving-window test, or Yang--Mills counterexample is
inferred. Sharper JOINT signed estimates remain eligible.

Independent finite QFT proposition selected: the actual incoming/outgoing
left/right Gauss sum on `baseLinks width` kills `spatialWeight w K width`
and intertwines the ORIGINAL `transferStep`. Its consumer is fixed-slice
gauge preservation before completed physical-domain/continuum transport,
not the horizontal energy or changing-family margin. Existing inputs are
the per-face original Gauss-zero law, raw closed-word/plaquette pins,
injective block embedding and `productMap_angular_carrier`.

Produce actual angular differentiation under that injective embedding
first; do not differentiate a padded equality or infer subset invariance
from the full-product law. Then transport the slice generator and reflect
the zero law on the same supported source. Test empty/zero-width slice,
off-image blocks, both frames, arbitrary nome and K=0. Predicted outcome:
an exact finite all-parameter identity, no analytic premise. Budget: two
bounded leaves, <=650 combined lines, <=4 focused checks, serialized
20-GiB worker/12-GiB reserve with fresh dynamic preflight each time.
Abandon/revise if a raw derivative pin is missing, support reflection is
unavailable, or the construction only assumes spatial gauge invariance.
Static author budget refinement: allow the actual instance up to 430 lines
for frame support, the full/filtered link-sum join and kinetic null propagation;
the combined 650-line/four-check/resource budget is unchanged. The optional
terminal-message consequence must not displace actual transfer preservation.
Selection is not proof evidence; the canonical chart and Clay status stay
unchanged. The main signed moving-moment/innovation estimate remains OPEN.

Observed implementation budget, before the next launch: core check 2 passed;
both instance checks rejected. Independent complete-source mathematical review
still finds no missing premise, but the second log isolates wasteful six-way
frame candidate search/unfolding, a missing namespace, one untyped tail sum
and a mis-parenthesized padded composition. Revise ONCE to five focused checks
total: one final instance attempt after six direct frame cases with a local
polynomial transparency shield and explicit typed compositions. Keep 650
combined source lines, all statements and 20-GiB/12-GiB safety limits unchanged.
If this last check fails, retain only the checked core in the Lean import tree
and record the unfinished transfer join, rather than continue a compiler loop.

## PAPER direct smoothed-window screen: pay the early box, not a raw reserve

2026-10-08 UTC, source review through `ef6f6120`; root mathematics and three
bounded independent read-only Sol reviews. No Lean edit, compiler run, new
`sorry`/axiom or new proof claim. The repeated lattice-measurement attachment
is already incorporated in `RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`;
its numerical result supplies neither the following moments nor a physical
operator identification. This section changes the analytic search criterion,
not a canonical frontier type or displayed proof state.

### Actual consumer and available inputs

- `lean/YMGap/Continuum/BF4WilsonAllNomeShiftedWindowSurvival.lean:448`,
  `PathShiftedWindowSurvival`, asks for theta*R_Y(N/2)<=R_Y(N+1).
  `:467`, `pathShiftedEpsBound_of_windowSurvival`, consumes precisely that
  backward window. The stronger raw-source short-time ratio is NOT its type.
- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:305`,
  `afPaddedZeroMomentumTrajectory`, keeps M=N=side(j), the original signed
  spatial family, its actual nome and its width. Its rational two-loop-shaped
  schedule is not a produced physical RG/spacing identification.
- `lean/YMGap/Continuum/BF4WilsonAllNomeSmoothedCoherentState.lean:326`,
  `smoothedResponse_orbit_expand`, and `:341`, `smoothedResponse_pin`, retain
  every double-orbit term and pin it to ORIGINAL centered family moments.
- `lean/YMGap/Continuum/BF4WilsonAllNomePositiveOrbitResponseOrder.lean:257`,
  `response_crossRatio`, proves the cleared block-ratio order without a
  nonzero-response premise.
  `lean/YMGap/Continuum/BF4WilsonAllNomeOddResponseJensen.lean:242`,
  `response_le_of_le`, supplies
  lag monotonicity on this SAME completed vector/operator.
- `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:110`,
  `family_time_geometric_floor`, and
  `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:151`,
  `familyExcitation_norm_floor`, give a positive rational floor for each
  moving response of a padded, nonzero coefficient family. The actual
  nonzero unit-coefficient family is constructed by
  `lean/YMGap/Continuum/BF4WilsonAllNomeShiftedPaddedNondegenerate.lean:251`,
  `paddedZeroMomentumTrajectory`. These are parameter-dependent floors,
  not the useful relative credit required below.

### Root-checked mathematical deduction, still PAPER

Fix ONE family member first. Write R_x(k)=B(x,T^k x), N=side(j), M=N,
p=N/2 and h=N+1-p. Thus p+h=N+1 without a rounding assumption.
For j>=1, N is even and h=N/2+1. Set r_s=R_x(p+s), and

    tau_s = s+1                 (0<=s<=N),
            2*N+1-s             (N<s<=2*N).
    (N+1)^2 R_Y(p) = sum_(s=0..2*N) tau_s*r_s.

The triangular recoding here is a PAPER counting identity derived from the
checked double sum; no new Lean declaration for it is claimed. Split at
0<=ell<=2*N+1 and set

    E=sum_(s<ell) tau_s*r_s,       F=sum_(s<ell) tau_s*r_(s+h),
    Tail=sum_(s>=ell) tau_s*r_s,   a=r_ell, b=r_(ell+h).

For each s>=ell, `response_crossRatio` with L=p+ell and j=s-ell gives
a*r_(s+h)>=b*r_s. Multiply by the nonnegative tau_s and sum. Exact expansion
then yields the unconditional PAPER lower bound

    a*(N+1)^2*[R_Y(N+1)-theta*R_Y(p)]
      >= a*(F-theta*E)+(b-theta*a)*Tail.

Consequently payment of this JOINT signed right side suffices, using the
already available positive rational floor for a to reflect scalar order.
No inverse of a completed-state norm or choice of a spectral measure is
required. If a=0, this cleared bound alone proves no survival; positivity is
an explicitly supplied existing family fact, not silently cancelled.
The identically zero coefficient family requires a separate trivial branch;
signed TIME filters are not covered by this positive-box argument. Individual
zero spatial coefficients are allowed when their squared sum is positive.
The original signed spatial coefficients are retained in x.

A conservative four-moving-moment screen follows for ell<=N+1 and theta>=0.
Let e=ell*(ell+1)/2 and t=(N+1)^2-e. Monotonicity gives E<=e*r_0 and
Tail>=t*r_(2*N), while F>=0. Therefore

    b>=theta*a,
    (b-theta*a)*t*r_(2*N)>=theta*a*e*r_0

are sufficient. Do not assert this test is necessary; keeping F may improve
it. The cheapest first split is ell=1: e=1, t=N*(N+2), and only the original
moments at lags p, p+1, N+2 and p+2*N occur. Every mean, normalization,
nome, width and source remains that of the fixed original family member.
Odd/even lags retain their distinct already checked scalar pins; no finite
stationary center or identification of separate chronological masses is used.
The actual changing-family credit b-theta*a and its early-mass payment are
NOT supplied by any inspected declaration.

### Cheap decisive test and decision

Exact BigInt rational arithmetic, NOT a Lean certificate/Yang--Mills instance:
take R(k)=(1/2)^k+N^(-2)*(1-1/(4*N))^k. For N=16,32,64 and theta=1/2,
the ell=1 four-moving-moment test and the literal double-box survival both
pass, whereas R(2)<=3*R(1)/5 in each case. The raw two-moment rate is far
from one; the later-window test can still work. A single fast mode R(k)=(1/2)^k
fails the late credit for h>=2, so positivity/smoothing alone has not been
turned into survival. These finite diagnostics select a weaker search
criterion; they are not original interacting moment bounds or proof evidence.
Independent read-only mathematical review PASS; all diagnostic inequalities
were independently reproduced with exact rational arithmetic, not Lean.

Continue the ORIGINAL later-window credit/early-mass analysis in parallel
with the already pinned last-window relative innovation. Do not make useful
raw R(2)/R(1) an additional mandatory premise. No new conditional compiler
is selected: before formalizing this reduction, derive a useful actual
changing-family credit/payment or show that the sharper joint test materially
reduces a produced estimate. Stop a wrapper-only branch with no such input.
All scaling, physical mass, continuum/QFT, every-group and Clay requirements
remain OPEN; canonical chart claims are unchanged.

### Other reviewed routes: preserve their actual residue

The original Ward payment is pinned by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`,
`original_ratioNoise_gradientPayment_weighted_pin`, to the density
m=V*a*T(Vbar*Ta), not a vacuum weight or a^2. For F=m*sum_r(J_r phi_k)^2,
the concentration identity's signed derivative contains BOTH

    YF=sum_i(J_i X)*[(J_i m)*sum_r(J_r phi_k)^2
                       +2*m*sum_r(J_r phi_k)*(J_i J_r phi_k)].

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseDerivative.lean:157`,
private `derivative_transfer`, keeps J(V*p) inside the actual kinetic map.
Time smoothing does not delete JV, the ratio Hessian or the antipodal term.
No inspected source producer pays these jointly in the SAME warmed variance.
The arbitrary-gradient antipodal diagnostic below neither proves nor refutes
the selected filtered family's estimate. No additional curvature-only leaf
is selected. Historical omitted-theta-cell instructions later in this audit
are superseded:
`lean/YMGap/Continuum/ThetaParityDiamondTail.lean:445`,
`frequency_box_factored_error_close`, already supplies the actual omitted-cell
join; `lean/YMGap/Continuum/ThetaProductRadialCeiling.lean:100`,
`productRadialCostCReal_le_cap`, and
`lean/YMGap/Continuum/SU2QuaternionPairedFrozenJacobiCurvature.lean:83`,
`frozen_curvature_certificate`, already supply the radial ceiling and full
frozen-direction witness. Do not rebuild these completed prerequisites.

The independent finite fixed-slice Gauss/transfer route is feasible but NOT
closed by the full-slab Ward result. Plane commutation exists at
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularCommutation.lean:56`,
`productMap_angular_carrier`; the slice still needs its actual spatial-action
Gauss-zero law, signed-frame/sum transport and Haar-null input propagation.
The expected G*T=P*G(V·) identity cannot silently assume G(V)=0 or differentiate
the existing padded slab-to-slice placement pins. This independent QFT input
is parked, not presented as a horizontal energy bound or a new proved node.

## Selected integrated-head centered score bound (2026-10-08 UTC)

Test a genuine stronger estimate, not another assumed reserve: with I the
actual head Haar integral and J acting inside that prefix, produce

    Certificate tail [C^2*det(W,f) - I((J W)*f)^2].

Argument: I(J W)=0 coefficientwise; the two ACTUAL positive laws C*W+J W
and C*W-J W have equal mass C*I(W). Half the sum of their variance
determinants is exactly the displayed polynomial. Unlike the existing
conditional Gruss bound, this result has no extra squared polynomial mass.
No mass inverse, positive source floor or strict C hypothesis is necessary.

Existing inputs: `SU2QuaternionMultiHeadVarianceReplica.determinant_certificate`,
`SU2QuaternionHaarAngularIBPAt.partialHaarHeads_angularDerivative_at_zero`,
and the ORIGINAL odd-marginal
`BF4ExactSlabFixedSpatialMarginalRelativeBound.frameRelativeBound`.
Actual consumer/instance: the selected active-link conditional score of
V*g_n*g_(n+1), retaining the full spatial action, both messages and every
shared tail variable. The cap is explicitly 6*relativeCap(w,4096)+
2*relativeCap(w,32), independent of width and depth at fixed nome and
sufficiently late cutoff. Use supported arbitrary signed tests, including
the original OWN-centered source after the actual head swap. This does NOT
yet pay last-window relative innovation or changing-family source retention.

Prediction/test: preserve the negative conditional first-moment square;
check W=0, C=0, f constant, signed f and shared tails. Stop if the result
duplicates an existing certificate, needs division by a polynomial mass,
changes the action, or assumes the desired estimate. Bounded experiment:
one algebra leaf plus one actual original instance, <=600 combined lines,
<=3 focused checks, one 20-GiB worker/12-GiB reserve and fresh preflights.
Sol handles finite algebra; root owns verification and complete-source
review, with independent mathematical screening in parallel. Selection
alone is not proof evidence and changes no canonical chart field.

### Verification-budget revision

Core check 1 passed. Original-instance checks 1--2 exposed accidental action
unfolding and an explicit 4*0+i versus i argument mismatch. The third
planned check was therefore not accepted proof evidence. Revise with local
transparency shields already used by adjacent original-action modules and
explicit natural-index normalization on BOTH the input bound and output.
Allow ONE additional focused attempt for that deterministic transport fix;
no memory, heartbeat, recursion, axiom or mathematical premise is increased.
Stop and report the unverified instance if this revised attempt fails.

### Observed: centered integrated score certificate CHECKED

`lean/YMGap/Continuum/SU2QuaternionIntegratedScoreVariance.lean:79`,
`centeredSignedSquare_certificate`, constructs the half-sum bracket directly;
`integratedAngularScore_certificate:147` produces I(J W)=0 by head IBP.
No C positivity, conditional-mass inverse or cancellation inside the cone.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialIntegratedScoreVariance.lean:59`,
`original_marginal_integratedScore_certificate`, instantiates the complete
original odd marginal; `paddedSquare_own_integratedScore_certificate:99`
retains the literal square and chronological OWN center. The actual bound is

    I((J W)*f)^2 <= C^2 [I(W)*I(W*f^2)-I(W*f)^2].

Every tail coordinate remains shared, including all surrounding action
dependence. Arbitrary supported signed tests and generic zero masses/C remain.
The original instance has its existing strict nome, late cutoff and physical
active-link guards, with explicit C=marginalScoreCap(w). This is an ORDINARY
conditional Haar estimate, not an OS quotient/transfer/scaling theorem.

Accepted focused checks: core attempt 1 and original-instance attempt 3.
All FOUR public printed gates are exactly {propext,Quot.sound}; no warnings
or sorryAx in either accepted log. Failed instance attempts 1--2 and their
downstream error-generated sorryAx are NOT accepted evidence. Four total
attempts, including the explicitly revised one-check budget. No resource
increase, new sorry/axiom/Classical/native premise, field weakening or broad
audit/guard/metric. Fresh process/memory checks before EVERY launch reported
86--87% memory headroom, zero swap; one monitored 20-GiB worker and 12-GiB
reserve throughout. Root inspected both complete final sources; independent
COMPLETE final-source review PASS at the frozen hashes below. Root imports
are registered ONLY, not root-built.

```text
Core: 166 lines, SHA256
13486676f9a2a70e122c670708a1b88aa0de12216a8aa1f6c337683a804117ab
/private/tmp/ym-oct8-integrated-score1.log, SHA256
a36489475a85f000d7462b17d79f3de676e226ef6b61ed310974095d6b1696cc

Original instance: 125 lines, SHA256
968185bad03f5d76987e2113870ba6fff412aeecb70402636ed950d3ec2aae99
/private/tmp/ym-oct8-original-integrated-score3.log, SHA256
ab14df9506761b313d76213dcacc126345a11b02b068b70e08781843d417c5cc
```

Decision: retain the stronger actual conditional certificate; PRUNE more
generic lower-floor/trace wrappers. NEXT remains the full ORIGINAL signed
cost versus SAME surviving filtered variance, or actual three-moment slow
overlap on a justified changing family. Neither an upper innovation reserve
nor useful raw retention follows from this local result. No canonical chart
claim changes; physical mass, continuum/QFT, every group and Clay remain OPEN.

### Independent mathematical screen (not a new proof claim)

The half-sum estimate is not exported by the inspected Gruss/dual-square
modules: their centered certificates retain an extra I(W)^2. Construct the
stronger bracket from the two determinants; do not cancel that polynomial
inside `Certificate`. Zero masses and C=0 must remain covered.

PRUNE a duplicated qualitative covariance/prediction-floor branch:
`QuaternionHaarRelativePredictionFloor.raw_prediction_floor:107` and
`normalized_prediction_floor:151` already give the relative-Ward floor;
`BF4ExactSlabRelativePredictionError.raw_prediction_bound:75` and
`finite_prediction_floor:137` produce its original-action instance.
The posterior trace contraction is a possible sharper PAPER consequence,
but no additional floor module is selected. Such LOWER floors do not give
the required UPPER innovation estimate or slow-state overlap.

The integrated-head estimate cannot silently replace the output-tail score.
`BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.ratioNoiseDensityMoment:74`
contains K*J(Va), not J(K*Va). The omitted (J K)*Va is load-bearing when
using head IBP. Continue only with the entire signed original correction,
not an assumed zero marginal for that partial density derivative. The
existing `BF4ExactSlabFixedSpatialScoreCalibrationObstruction.marginalScoreCap_formula:63`
and `gap_score_square_ge_one:83` also prevent treating the computed C^2
envelope as the missing small weak-coupling energy coefficient. These are
existing results, not re-proved or counted as new progress here.

## Selected source-preserving smoothing comparison (2026-10-08 UTC)

Previous turn PROGRESS: d1e21f87 checks the original noise/cost comparison.
The useful source-specific relative reserve remains unproduced. Independent
source reviews find no useful three-moment margin in the existing absolute
radial cap: its coefficient tends to one in the AF bare-transmission probe,
and an absolute upper bound supplies no favourable signed gain. Retain the
OWN-mean correction in the original signed source-defect pair.

Reuse its EXISTING boundary payment rather than build another centering
wrapper: `own_centeredMeanPair_bound`, `own_meanResidue_bound` and
`own_meanResidue_tolerance_bound` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredMeanResidueBound.lean:138`,
`:195`, `:241` give |M|<=4*q^n*Z2 and
|(lambda-1)*c*M|<=8*(1-lambda)*q^n*Z2, with the computed
`meanResidueDepthCutoff:235`. This pays normalized fixed-member boundary
error, not useful relative gain or a physical family reserve. The finite
OWN mean centers the ODD density a*Ta, not a^2; do not assume its even
centered first moment is zero. No new estimate is counted for this review.

The next selected unconditional mathematical proposition is

    R_x(L+j+h)*R_x(L) >= R_x(L+j)*R_x(L+h).

For any nonnegative rational orbit weights and Y=sum_i c_i*T^i*x, the exact
double-orbit expansion would then give

    R_Y(L+h)*R_x(L) >= R_Y(L)*R_x(L+h).

Actual consumer: reduce the separate smoothed-source relative retention
estimate to a raw-source ratio on the SAME completed carrier. The raw ratio
is NOT supplied; smoothing cannot create absent slow-mode overlap. The
two-state positive Markov test with eigenvalue 1/2 retains a nonzero warmed
box-filtered source but has block norm ratio 4^(-d), independently of the
filter radius. This is a PAPER scope test, not a Yang--Mills counterexample.

Available inputs: `BF4WilsonAllNomeOddResponseJensen.response_log_convex_step`
at `lean/YMGap/Continuum/BF4WilsonAllNomeOddResponseJensen.lean:222`, actual
second-defect positivity, and `smoothedResponse_orbit_expand` at
`lean/YMGap/Continuum/BF4WilsonAllNomeSmoothedCoherentState.lean:326`.
Prediction: adding a rational epsilon>0 gives produced positive floors;
the local log-convex determinant gains epsilon times the positive second
difference. Finite cross-ratio induction and existing constructive
positive-factor cancellation, followed by zero-safe order closure, remove
epsilon. No representing measure, tensor carrier, norm inverse or new
analytic premise is selected. Test zero states, fringe time-kernel states,
arbitrary signed raw sources, h=0, and repeated positive orbit lags.
Stop/revise if a source floor must be assumed, an action/operator is changed,
or the argument needs a new analytic framework. Budget: one Sol leaf <=600
lines, <=3 root-owned focused checks, one monitored 20-GiB worker/12-GiB
reserve with fresh dynamic-capacity checks, and independent complete-source
review. This selection is not proof evidence or a change of chart state.
No further innovation/conditional-survival identification wrapper is selected.

### Observed: zero-safe positive smoothing order CHECKED

The selected comparison is now proved in
`lean/YMGap/Continuum/BF4WilsonAllNomePositiveOrbitResponseOrder.lean`:
`response_crossRatio:257`, `positiveOrbit_response_crossRatio:305`,
`shifted_response_floor:343`, and `positiveOrbit_response_retention:387`.
An actual raw retained fraction transfers to positive rational time-orbit
smoothing on the SAME original completion, without a source-norm floor.
Scalar regularization supplies its own positive floor and is then removed
by explicit convergence/order closure. Zero responses, empty orbits,
repeated entries and arbitrary signed raw sources remain; signed filters
are excluded. Raw retention is sufficient, not a new necessary hypothesis.

Final source: 415 lines, SHA256
`77b2f78e11550198e0fba5657827f58d786877d2aab08680bb42c8c58f022f2f`.
Accepted focused check 2: `/private/tmp/ym-oct8-positive-orbit-order2.log`,
SHA256 `cf1d18a3f29234d313f417ddc00cc598ebccd83d0221ca1e763c4cd3c873d75c`.
Nine printed gates: `invSucc_converges_zero` uses only {propext}; the other
eight use {propext,Quot.sound}. No errors, warnings or sorryAx. Check 1
failed on notation-shadowing binders and natural-addition normalization;
its failed downstream gates were not accepted. The repaired final source
passed COMPLETE independent review at the stated hash. Both launches used
ONE monitored worker, 20-GiB cap/12-GiB reserve and fresh capacity/process
checks (87% reported headroom, zero swap). Root import registered ONLY;
no root/tree build, broad audit, guard or metric was run. No new hole,
axiom, classical step, resource option or analytic premise.

This removes separate positive-double-orbit retention work WHEN a raw
reserve is produced; it does not produce useful changing-family overlap,
signed credit or relative innovation. NEXT remains their actual analytic
estimate, not another propagation wrapper. Physical mass, continuum/QFT,
every-group/Clay and canonical displayed claims remain unchanged.

## CHECKED quantitative last-window noise/cost join (2026-10-08 UTC)

Previous goal turn PROGRESS: 2f0ef648 checks the complete signed prediction
payment. The new UNCONDITIONAL comparison of the actual original cost L
and cleared last-window innovation Z*ell(N_k):

    abs(L-Z*ell(N_k)) <= (eta+2*q^k)*W*B.

Here a=g_(n+t), b=T^t(g_n*psi), U=T^d, Z=ell(a^2), W=ell((Ua)^2),
B=ell(b^2), L=W*B-Z*ell((Ub)^2), and N_k=blockNoise_d(a,phi_k).
The exact split below, original block-noise variance law and checked joint
prediction supply all algebraic inputs. The finite drift join is
the original TerminalRayleighDrift argument with terminalComparison(s,2d,0),
not a new analytic assumption. That bound is now produced on the existing source.
Retain zero norms, d=0, arbitrary signs and BOTH masses. <=360 added lines
across the two EXISTING leaves, <=3 root-owned focused capped checks and
complete final-source review. Observed output: +261 lines, three focused
attempts within budget, both final checks and COMPLETE independent reviews
PASS. The useful noise is pinned to the ORIGINAL transfer cost, without
paying its unknown relative bound or adding an analytic premise.

Exact new public declarations:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalRayleighDrift.lean:228`,
`futureBlockDrift_bounds`, and `futureBlockDrift_abs_le:297` supply both
signed/absolute orders at every future block r, including r=0. At r=2d,
weighted symmetry pins its mixed mass ell(a*T^(2d)a) to W=ell((T^d a)^2).
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedPredictionPayment.lean:505`,
`blockConditionalRatio_noiseCost_abs_le`, proves the displayed discrepancy
bound for the ACTUAL reciprocal, arbitrary supported signed psi and degree k.
Its checked noise endpoint/difference-of-squares split retains every original
spatial factor and both chronological masses. Zero norms/rates, d=0 and any
unchanged rational OWN stage center remain; no inverse norm, stationary pin,
source overlap, noise ceiling or retention estimate is assumed.

Final drift source (317 lines), SHA256
`dfa1048c6b2b28b70e0823f89fa03c7d3103f9e4f6f564eee93fe3a5bf9316c5`;
log `/private/tmp/ym-oct8-future-block-drift2.log`, SHA256
`9f2aa669516d46c95af1b8b87d0a10912ea5902ddf6d59de6dddb1a16cc127f9`.
Final combined source (605 lines), SHA256
`4546e22e6336763f66c16d29940fa1f22f20d4ad9b2c32a99f1864b2810940fc`;
log `/private/tmp/ym-oct8-noise-cost-pin1.log`, SHA256
`d39a46e3df8d362093dcc67cb33f1b20552a9eed23aef6da82c299b0167db161`.
Six drift-file and ten combined-file gates exactly {propext,Quot.sound};
COMPLETE independent FINAL-source review PASS at both hashes. The earlier
drift check failed only a leading-negation conjunction parser layout; its
failed new gates were not accepted. Root parenthesized the statement without
changing its mathematics; repaired drift and first combined check PASS.
ONE monitored worker, 20 GiB cap/12 GiB reserve, fresh capacity/process checks,
87% reported memory headroom and zero swap. Existing root imports unchanged;
no root/tree build/audit, guard or metric. No new module/hole/axiom/resource
option. The finite cost/noise join is now CHECKED; completed retention from
an eventual relative innovation reserve remains PAPER, not an inhabited
producer. NEXT actual innovation/control OR original three-moment ratio and
overlap; no further identification/conditional-survival wrapper selected.
Continuum/physical/QFT/every-group/Clay and canonical displayed claims unchanged.

### Reviewed limit order: approximation onsets need not be family-uniform

Independent read-only source review, not a new Lean closure. Fix nome,
width, radius-zero expression and finite t,d before completing each member.
The actual diagonal K=headCutoff(w)+stage and boundary depth stage are controlled by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalJointCauchy.lean:57`,
`jointModulus`, and `originalJoint_diagonal_converges:128`.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalJointLimits.lean:79`,
`originalCutoffExpectation_converges`, and `boundaryTimeLimit_converges_joint:118`
identify the fixed-member iterated orders with its SAME joint limit.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.lean:158`,
`expressionEndpointMeanThreshold`, is explicit data;
`expressionOwnMean_converges:225` and `expressionOwn_centeredPair_converges:251`
keep the moving OWN center. `lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:130`,
`originalOwnBlockVariance_converges`, and `originalOwnBlockCost_converges:143`
reach its completed moments and lag differences.

Consequently eta_stage and q^k may be paid by member-dependent explicit
depth/reciprocal cutoffs BEFORE the changing-family comparison. A common
bound on these auxiliary depths is not necessary for THIS passage.
No limit of phi_k or N_k is needed if only the original cost/variance
inequality is passed. A sufficient PAPER analytic input is: for every
rational epsilon>0, eventually in stage, SOME k with 2*q^k<=epsilon has

    Z_stage*ell(N_(stage,k)) <= (1-kappa+epsilon)*W_stage*B_stage.

With eta_stage<=epsilon, the finite reserve is kappa-3*epsilon. Its two
variance quantities are independent of k; their existing convergence plus
arbitrary-epsilon order closure would give completed retention. This late
stage relative innovation bound is NOT produced; neither uniform positive
kappa, physical rate calibration nor changing-source convergence follows.
This removes an unnecessary approximation-onset demand, not a Clay field.
The cited OWN-expression pins carry Within 0. Already-smoothed sources
retain their full double-orbit/OWN-center joins; they are not silently
identified with a new radius-zero source.
The finite cost/noise join is now checked above; the completed retention
consequence remains PAPER.

### Direct alternative: reuse the three-moment shifted-ratio test

Independent source review: `lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:117`,
`response_geometric_lower`, already propagates rho*R(0)<=R(1) without
a norm inverse or positive floor. More usefully,
`lean/YMGap/Continuum/BF4WilsonAllNomeBlockResponseLower.lean:129`,
`response_shifted_block_geometric_lower`, propagates a ratio at ANY start.
For start=1,step=1, test just the cleared inequalities

    rho*R(1)<=R(2),   alpha*R(0)<=R(1),
    kappa<=alpha*rho^(N-1),   N>=1, rho,alpha>=0.

They suffice for ORIGINAL source retention R(N)>=kappa*R(0), not retention
of a replacement normalized state. These are only three ORIGINAL moments;
the overlap alpha is not free and must be produced. Prefer the existing
block-Bernoulli consumers to huge rational powers at growing horizons.
No new Jensen/Bernoulli or moment-wrapper leaf is needed. The useful actual
changing-family ratio and overlap remain unproduced.

Exact-rational PAPER diagnostic, not a YM instance or Lean certificate:
two modes with eigenvalues 0 and r=1-1/N and equal weights give
R(0)=1,R(1)=r/2,R(2)=r^2/2. At N=4,8,16,64, Python Fraction verifies
the shifted ratio rho=r, overlap alpha=r/2 and macro reserve >=1/8;
the raw lag-one geometric floor is <1/8 and the cubic truncation is negative.
This shows why slow-component overlap must be paid separately and why the
three-moment screen can succeed where raw/cubic certificates fail. It does
not produce those moments for the original interacting action. The original
innovation/curvature route remains co-primary; no field is strengthened.

## CHECKED joint signed prediction payment (2026-10-08 UTC)

Previous turn PROGRESS: 75febcfd supplies arbitrary supported-input Schur.
The new exact estimate uses C=W*Id-Z*T^(2*d), Z=ell(a^2), W=ell((T^d a)^2).
It produces Z*||T^d r||^2<=S*W*||r||^2 for EVERY supported r from the actual
terminal bracket, S=(1+comparisonEta(w,width,m-1))^2. Applying this to
T^d r and retaining symmetry in the squared expansion yields

    ||C r||^2 <= W^2*||r||^2+(S-2)*W*Z*||T^d r||^2.

At the existing fixed-nome/width drift-depth cutoff for tolerance 1/4,
S<=25/16<=2. For the ACTUAL reciprocal prediction p=a*phi and e=b-p,
produced ||p||^2<=B, ||e||^2<=delta^2*B give, by Cauchy--Schwarz,

    abs(W*ell[e*(b+p)]-Z*ell[(T^d e)*(T^d(b+p))]) <= 2*delta*W*B.

This is the entire signed prediction correction in original currency;
the old separate-cross PAPER cap was 2*delta*(1+S)*W*B. No inverse B,
square root, stationary pin, useful norm-bound assumption or action change.
Available inputs: arbitrary Schur leaf above; `filteredTerminalBracket` and
`filtered_terminal_partition_lower` in FilteredVarianceComparison; actual
weighted transfer symmetry; existing BlockConditionalDrift multiplier bound,
BlockConditionalRatio reconstruction and explicit fixed-parameter depth
cutoff. Root mathematical selection, Sol bounded implementation and
independent read-only review. The <=480-line/<=3-check budget produced a
430-line leaf passing focused check 2 and complete FINAL-source review.
Zero source norm, d=0, arbitrary signs and possible negative spectrum of C
remain; positivity of C is neither supplied nor assumed. The last-window
innovation estimate and source-weighted radial/antipodal/original-deficit
payment remain OPEN. This ordinary original spatially weighted polynomial
norm is NOT an OS quotient or a completed/physical gap theorem.

Observed declarations, all in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedPredictionPayment.lean`:
`original_arbitrary_normalized_schur_le:180` produces the normalized
arbitrary-input Schur bound; private `onset_factor_le_two:240` produces
S<=2 from the EXISTING explicit fixed-nome/width cutoff at tolerance 1/4;
`original_signed_prediction_square_le:256` proves the C-square bound;
`blockConditionalRatio_signedPrediction_abs_le:349` pays the ACTUAL finite
reciprocal's complete signed correction by 2*mixRate^k*W*B. Both chronology
masses, supported signed source, m>=1 and original head cutoff stay explicit.
No inverse norm/error rate, stationary law, source cap, replacement action
or analytic operator-norm premise. The onset is NOT scaling-uniform.

Final source SHA256
`c127cedabddd49fb1da587c757377dc2a6d028d485a0204f466694d999cbf2c0`;
log `/private/tmp/ym-oct8-signed-prediction2.log`, SHA256
`5d255708e73eeca914639e6fc0123fa7eef867c46ac2b37b5ee3506181354c8e`.
All six printed gates exactly {propext,Quot.sound}; independent COMPLETE
FINAL-source review PASS at that hash. Check 1 failed on match layout and
local-definition unfolding; its failed main gates were NOT accepted. Two
local repairs, no mathematical statement or resource-option change; check 2
PASS. One monitored worker, 20 GiB cap/12 GiB reserve, fresh process/capacity
preflight and zero swap. Root import registered only; no root/tree audit,
guard or legacy metric. Canonical displayed claims unchanged.

Independent source screen: `original_lastStep_score_dissipation_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialScoreDissipation.lean:138`,
bounds score BY loss; it must not be inverted into a noise upper bound.
The minimum remaining cleared input is Z*ell_V[blockNoise_d(a,phi_k)]
<=epsilon*W*B. Together with the PAPER last-window split, terminal drift
and the CHECKED joint payment, epsilon+eta+2*q^k<=1-kappa would suffice.
This is not a produced epsilon or survival certificate. The exact Ward
payment at RatioNoiseWardAbsorption:384 keeps T(Vbar*Ta); its signed
J(V*a), J(Vbar) and differentiated original-prefix deficit still need
joint original-norm control. No additional hypothesis wrapper is selected.
DIRECT original macro retention remains a co-primary alternative.

## Generic ORIGINAL terminal Schur: checked missing error join (2026-10-08 UTC)

Previous goal turn: PROGRESS, commit d1a0690e checks the actual finite
Jacobi lower log-Hessian. Its scope/remaining source-weighted joins are
recorded below; it is not a changing-family gap proof.

Exact selected proposition, now CHECKED: for every supported r, actual a=g_m with m>=1,
and the existing terminal upper certificate U*a-T^d*a>=0, prove

    ell((T^d*r)^2) <= U^2*ell(r^2).

The missing instance is r=e=b-a*phi in the last-window noise identity.
The current `original_block_terminal_schur_source_le` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSchurClosure.lean:109`
accepts only a transmitted source. No original polynomial preimage for e
is supplied or assumed. The terminal bracket itself is PRODUCED by
`terminalComparison` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalComparison.lean`; the
generic estimate must not assume a useful operator norm instead.

Available proof inputs: `original_block_terminal_schur_square_le` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSchurTest.lean:84`;
`multiplierSquareCertificate` at
`lean/YMGap/Continuum/QuaternionHaarPositiveWindowInverse.lean:186`;
`reciprocal_weighted_error_le` at
`lean/YMGap/Continuum/QuaternionHaarReciprocalWeightedError.lean:60`;
and `originalBlockTransfer_weighted_square_le` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWeightedContinuity.lean:98`.
The actual terminal window at n=m,t=0 supplies its lower/upper certificates
and `blockWindow_radius_pin` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:250`.
Take G_k to be that finite reciprocal and p_k=a*G_k*r. Its square is <=the
SAME input square, and its reconstruction error is <=mixRate^(2k) times
that square, without a source interval/cap. Polynomial Schur pays p_k;
the coarse continuity cap only pays the vanishing remainder. Existing
rational Young/order closure removes it from the conclusion.

Prediction: the precise existing closure argument works for arbitrary r
once these two approximation estimates are instantiated generically.
Decisive edges: zero input/norm, d=0 and all signs, with no division by norm;
the m>=1 guard stays because the terminal window is the actual input.
Verification budget: one leaf <=360 lines, no resource-option increase,
at most three focused root-owned checks and complete independent final
source review. Abandon/revise if the direct generic estimates need another
analytic framework. Do not add a normalized/retention/Schur-hypothesis
consumer instead of this missing inequality. The actual last-window
innovation, SAME incoming-weight concentration and physical scaling remain
unproved. No chart node changes from selecting this task.

Observed output: `original_block_terminal_schur_arbitrary_source_le` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSchurArbitrarySource.lean:203`
proves exactly the selected arbitrary-input estimate. Its generic multiplier
and reconstruction proofs are `reciprocal_square_le` at :105 and
`reciprocal_reconstruction` at :140 in the SAME file. Both rational order
closures remove the coarse continuity cap; no positive input-norm premise,
transmitted preimage, source cap, stationary law or analytic operator-norm
input is added. m>=1, strict nome and the actual terminal certificate remain.
Zero norms and d=0 are retained. This is ordinary original spatially weighted
L2, not an OS-quotient or physical/continuum gap theorem.

Verification: first focused check PASS, final 296-line source SHA256
`5a6535e8c14542c87e0addffe7e39aa68fbc818e2b02e58bbf1c9ba21048dd9f`.
Log `/private/tmp/ym-oct8-arbitrary-schur1.log`, SHA256
`3c01f2825923127a220d1b3adb364b5fc3f9aaf189ce66835c5f93557f1d5b42`.
All three axiom gates exactly {propext,Quot.sound}; independent COMPLETE
FINAL-source static review PASS at the same hash. One monitored worker,
20 GiB cap, 12 GiB reserve; fresh process/capacity preflight, swap zero.
Root import registered only; no root/tree audit, guard or legacy metric.
Interpretation: closes the arbitrary prediction-error transfer join. The
joint signed prediction payment is now checked above; the full last-window
cost/noise comparison is now CHECKED above; its completed retention
consequence remains PAPER. The actual
changing-family relative innovation and all Clay requirements remain OPEN.

### PAPER screen: source-weighted concentration is not automatic

Independent read-only analysis, not a new Lean theorem. With unit relative
scalar X, delta=1-X, and YF=sum_i (J_i X)J_i F, actual angular IBP and scalar
jets give the paper identity

    H[F*(3*X*h-(1-X^2)*h')] = H[h*YF].

Inputs: `angular_pair_at`,
`lean/YMGap/Continuum/SU2QuaternionHaarAngularIBPAt.lean:120`;
`relativeScalar_second_jet`,
`lean/YMGap/Continuum/SU2QuaternionPairedFrameScalarJets.lean:129`;
`paired_first_jet` and `relativeWord_unit`,
`lean/YMGap/Continuum/SU2QuaternionPairedScalarSquare.lean:57` and :69.
For a nonnegative endpoint slope floor gamma, the resulting estimate retains
the signed derivative debt -H[h*YF] AND the antipodal term
gamma*H[h*F*delta^2]; the latter cannot be absorbed at X=-1.

A decisive PAPER test uses F_k=delta^k and g=delta^n, n>=1:

    (k+3)*H[(1+X)*F_k] = 3*H[F_k],
    G=sum_i (J_i g)^2 = n^2*(1+X)*delta^(2n-1),
    (2*n+3)*H[(1+X)*G] = 5*H[G].

For any fixed background m with literal bounds 0<L<=m<=U,

    L*(2*n+3)*H[m*G*delta]
      >= [2*L*(2*n+3)-5*U]*H[m*G].

Amplitude rescaling g by 2^n keeps |g|<=1 without changing this ratio.
Thus arbitrary bounded gradient-square insertions can concentrate near the
antipode even under a fixed positively bounded background. This prunes an
insertion-only universal concentration shortcut, NOT the actual selected
filtered source: no realization of these tests as that source is proved.
It is not a Yang--Mills counterexample.

The literal payment remains `original_ratioNoise_gradientPayment_weighted_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`:
H[V*a*(J phi)^2*T(Vbar*T a)]. An endpoint-kernel expansion must retain
the transferred factor, the derivatives of V*a and of J phi. Moreover
`prefix_split_pin`,
`lean/YMGap/Continuum/SU2QuaternionPairedHeatPrefixDeficit.lean:203`, and
`prefix_first_split_pin` at :209 retain the original character cutoff's
deficit from the weighted Jacobi derivative heat. NEXT is joint control of
these actual radial cross, antipodal and deficit contributions, not a
vacuum concentration theorem or another scalar-clock wrapper.

## Near-flat Jacobi-heat comparison: checked finite estimate (2026-10-08 UTC)

Status: finite scalar estimate CHECKED; paired and last-window consumers
below remain PAPER, with their unproved original/analytic joins explicit.
The repeated user lattice-measurement note is already reconciled in
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`. A targeted primary
reread confirms Morningstar--Peardon's Table 7 uses r0*m=4.21(11)(4), and
1730(50)(80) MeV after setting r0^-1=410(20) MeV; it does not measure the
note's quoted string-tension ratio. Its correlator selects states with
nonzero overlap, not every excitation. Creutz's abstract extracts the
Kogut--Susskind Hamiltonian by sending temporal spacing to zero, not by a
finite-spacing identity. Reuse the existing corrections and SAME-logarithm
consumer; no measured mass or smooth sample-connection premise is adopted.
[Morningstar--Peardon, sections II and VI](https://arxiv.org/html/hep-lat/9901004).
[Creutz, abstract](https://doi.org/10.1103/PhysRevD.15.1128).

Actual proposition proved: for the finite normalized Jacobi polynomial h_N,
0<w<1 and x>=0, the denominator-cleared lower log-Hessian bound is

    0 <= C_T(w)*h_N(x)^2+h_N(x)*h_N''(x)-h_N'(x)^2,
    C_T(w)=2*w/(1-w*w).

The finite moment pins are
`lean/YMGap/Continuum/JacobiHeatRadialMomentJets.lean:214`,
`heat_eval_moment_pin`; `:226`, `heat_first_moment_pin`; and `:242`,
`heat_second_moment_pin`. With Q=`normalizedProduct` they give
h=Q*M1, h'=Q*(M1^2-M2), h''=Q*(M1^3-3*M1*M2+2*M3).
Here h_N is the finite weighted normalized Jacobi derivative approximation,
not the original character-cutoff polynomial. It is defined by
`JacobiShiftedPositiveCoefficients.heat` at
`lean/YMGap/Continuum/JacobiShiftedPositiveCoefficients.lean:126`.
The proposed numerator is EXACTLY

    Q^2*((C_T-M2)*M1^2 + 2*M1*M3-M2^2).

`lean/YMGap/Continuum/JacobiHeatRadialMixtureCancellation.lean:112`,
`moment_variance_nonneg`, produces M1*M3-M2^2>=0. The remaining bound
M2<=M1<=C_T is produced from r_i=2*w^(2*i+1)/(1+2*x*w^(2*i+1)
+w^(4*i+2)) on x>=0, retaining the empty prefix. No reciprocal heat minimum,
volume coefficient, free Gaussian, or new analytic hypothesis is needed for
this FINITE rational estimate. The lower half is now checked; existing
log-concavity supplies the upper half on the intended scalar interval.
C_T is explicitly nome-dependent, diverging as w->1; the proved uniformity
is only in finite prefix. The rescaled coefficient below is not a physical
mass floor.

PAPER paired consumer: on 0<=X<=1, for R=sum u_i^2 and v=J_u X, geometry gives
v^2<=2*(1-X)*R. Thus the transverse term
(h*h''-(h')^2)*v^2 lies between -2*C_T*(1-X)*R*h^2 and zero.
The existing `JacobiHeatTransverseCurvature.transverseCap_nome_defect_le_one`
at `lean/YMGap/Continuum/JacobiHeatTransverseCurvature.lean:301` gives
(1-w)*C_T<=1, so the rescaled error coefficient is <=2. This does NOT remove
the radial slope or identify it with a physical Gaussian/curl clock.
Near-flat concentration must be proved under the SAME original source-dependent
insertion, not just vacuum: `RatioNoiseWardAbsorption.
original_ratioNoise_gradientPayment_weighted_pin` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`
retains ell_V[a*(J phi)^2*T(Vbar*Ta)]. The X<0 contribution and original-prefix
jet comparison also remain unpaid. Consequently no scaling/gap node closes.

Verification budget: one leaf <=350 lines, no option increases, at most three
focused root checks under the 20-GiB/one-worker policy, complete final-source
review. Abandon/revise if direct actual-factor bounds require a larger new
analytic framework; do not expand a Gaussian or curvature-assumption wrapper.

Observed output: `lean/YMGap/Continuum/JacobiHeatNearFlatLogHessian.lean`
has 183 lines, SHA256
`8c3c04cd8ab07bb341acafcdae97b15a57156a722d8bc4f72f1c5b63b746d319`.
Declarations: `sTerm_le_one:71`, `sTerm_le_transverseRate:82`,
`firstMoment_le_cap:92`, `secondMoment_le_first:101`,
`heat_logHessian_lower:142`. Root and independent reviewer completely read
the FINAL source; mathematical/scope review PASS including x>1 and N=0.
Focused check 1 found only the missing `QPolyFormalDerivative.pderiv`
namespace open; four auxiliary gates already passed, while the failed theorem's
diagnostic sorryAx was NOT a source hole. Root repaired that one open line.
Focused check 2 PASS, all five gates exactly {propext,Quot.sound}:
`/private/tmp/ym-oct8-nearflat-loghessian2.log`, SHA256
`4cf52f0a5547333e9ce7b61d3cccb6584f088fdb7cdfcc99051f2247c5004111`.
Both initial calls were terminal (0.69s/0.64s); no artificial wait or further
check. Before EACH launch, process inspection found no competing worker,
memory_pressure reported 84 percent headroom and swap usage was zero.
One hard 20-GiB worker/12-GiB reserve throughout, no option increase.
Root import registered only; no root/tree build/audit/guard/metric. No chart
claim or Clay-facing field changes. Continue to the actual weighted estimate,
not another half-line certificate or endpoint-slope/calculus interface.

Independent PAPER reduction of the direct macro route: with U=T^u,
a=U*g_n, b=U*(g_n*psi), A=U*a, C=U*A=g_(n+3u), Z=ell(a^2), W=ell(A^2),
and a supported polynomial prediction phi, set e=b-a*phi and
D_phi=A*U(a*phi^2)-U(a*phi)^2. Exact expansion/symmetry gives

    W*ell(b^2)-Z*ell((U*b)^2)
      = Z*ell(D_phi)+ell[a*phi^2*(W*a-Z*C)]
        +W*ell[e*(b+a*phi)]-Z*ell[(U*e)*(U*b+U(a*phi))].

No inverse conditional density or whole-history-noise subtraction occurs.
`BF4ExactSlabFixedSpatialTerminalComparison.terminalComparison_relative_width`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalComparison.lean:306`
with s=n+u-1,r=2u,t=0 and 1<=n+u pays the drift in absolute value by
comparisonEta(width,n+u-1)*W*ell(a^2*phi^2). No finite stationarity or
endpoint recentering is used. The actual last-window innovation relative to
W*ell(b^2) remains unpaid; the signed prediction correction is now CHECKED
at the explicit onset above, not at a scaling-uniform onset.
`blockConditionalRatio_reconstruction` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:281`
produces a SAME-warmed-norm reconstruction error. The new joint payment
constructs the transferred correction from it and arbitrary-input Schur;
do not add a consumer which merely assumes retention.

The earlier sharp terminal-Schur closure applies only to a transmitted
source: `original_block_terminal_schur_source_le` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSchurClosure.lean:109`.
PAPER extension to arbitrary supported r (including e) is possible with the
same actual positive terminal a and produced certificate U*a-T^d*a>=0:
approximate r by a*G_k*r, retain its relative square error and contractive
multiplier square, then let the coarse transfer-continuity error vanish.
Generic inputs are `reciprocal_weighted_error_le` at
`lean/YMGap/Continuum/QuaternionHaarReciprocalWeightedError.lean:60`, and
the polynomial Schur square at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSchurTest.lean:84`.
The GENERIC declaration is now proved in the arbitrary-source leaf recorded
above; it applies directly to e. Do not derive that instance from the older
transmitted-source specialization. No arbitrary observable/transfer preimage
is assumed.

Superseded PAPER separate-cross consequence using that checked generic join:
put B=ell(b^2), p=a*phi, and use the produced ell(p^2)<=B and
ell(e^2)<=delta^2*B, delta>0. With eta=comparisonEta(width,n+u-1),
S=(1+eta)^2, the normalized terminal Schur bounds give output square caps
S*(W/Z)*B for U*b and U*p, and S*(W/Z)*delta^2*B for U*e.
Rational Young applied to EACH of the four signed cross terms pays their
sum in absolute value by 2*delta*(1+S)*W*B. The CHECKED joint signed
prediction theorem above replaces this cap by 2*delta*W*B when the actual
depth meets its computed fixed-nome/width onset; delta=0 is retained.
No square root, source cap, unfiltered variance or surviving-norm inverse.
The terminal drift then costs at most eta*W*B, and the remaining sufficient
estimate, with that onset, is

    Z*ell(D_phi) <= [1-kappa-eta-2*delta]*W*B.

This is an ACTUAL last-window innovation relative to the warmed norm;
positivity alone cannot pay it. Generic closure is now CHECKED; this
changing-family analytic estimate remains OPEN, not an assumed survival
certificate. The composite four-cross payment is CHECKED; the
completed retention consequence remains PAPER, and full historical noise
is not needed for this reduction.
The actual multiplier bound is `blockConditionalRatio_surviving_square_le`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalDrift.lean:81`;
it is not a supplied nondegeneracy hypothesis.

## Direct cubic ORIGINAL-response estimate: checked output and scope (2026-10-08 UTC)

Previous goal turn: PROGRESS, commit `7604b6b2` supplies the actual signed
affine endpoint cap. The changing-family relative margin is still OPEN.
Before another filter consumer, select an unconditional estimate on the
ORIGINAL response itself. Put d_l=mixedMoment(x,0,l), R_x(N)=B(x,T^N*x):

    B_N = d_0 - N*d_1 + C(N,2)*d_2 - C(N,3)*d_3 <= R_x(N).

Available inputs: `lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectMoments.lean:343`,
`mixedMoment_nonnegative`, and `:349`, `mixedMoment_split`; existing exact
Pascal coefficients are `lean/YMGap/Continuum/PNPaths.lean:120`, `choose`.
The PAPER proof is simultaneous induction in N of the zeroth upper, first
lower, second upper and third lower bounds, at every defect order l.
R_(N+1,l)=R_(N,l)-R_(N,l+1); the alternating Pascal truncations have the
same recurrence, with the preceding truncation at l+1. The fourth-defect
remainder is positive. An equivalent nested sum ranges over
0<=i3<i2<i1<i0<N and is empty for N<4; do not use an inclusive range
0..(N-4) with truncated natural subtraction at small N.

Consumer: for z=T^t*x, a supplied actual bound kappa*R_z(0)<=B_N yields
the ORIGINAL kappa*R_x(2*t)<=R_x(2*t+N) by
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:158`,
`completedInner_time_sum`. At 2*t=N=side this feeds the direct macro route,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`,
`normalizedAnchorResponse_block_floor`, with its original state/guards.
No filtered norm or changed observable is required. The quantitative
changing-family cubic margin is NOT an available input.

Decisive diagnostic, exact rational arithmetic only, NOT actual YM moments:
on the strict two-mode vacuum complement diag(31/32,7/8), source weights
1/2, N=8, (d0,d1,d2,d3)=(1,5/64,17/2048,65/65536). The cubic is
4521/8192, while the existing first-moment Jensen floor is (59/64)^8;
their exact positive difference is 8509939557407/281474976710656.
Every endpoint-cap-one affine LINEAR telescope has floor <=3/8 here:
the faster mode's factor 1-N*(1-lambda) vanishes, and the slower mode
contributes at most (1/2)*(3/4). This demonstrates a stronger certificate
in a nondegenerate case; it is NOT uniform dominance over other filters,
a Yang--Mills counterexample, or a produced original margin. A pure slow
mode already has a useful existing Jensen floor, so it is not evidence
that the cubic alone opens a previously unavailable survival route.

Precision guard: at N>=3 the ordinary adjacent-moment coefficients of B_N
are (1-N+C2-C3, N-2*C2+3*C3, C2-3*C3, C3). For 0<kappa<=1, their
test B_N-kappa*m0 has exact coefficient-L1
kappa-1+2*N-4*C2+8*C3, of order N^3. An actual four-moment error <=epsilon
therefore needs strict excess above that coefficient times epsilon.
Dividing the test by N^3 also divides its margin; it does not remove the
precision requirement. Prefer actual scaled deficit estimates if available.
Complete monotonicity alone does NOT pay d2/d3's relative scale or B_N's
positive margin; fast components can make this cubic negative.

Independent PAPER limitation, using an ACTUAL polynomial square: for N>=3,
C3>0, alpha=C2/(2*C3), y=(I-T)z-alpha*z, positivity of mixedMoment(y,0,1)
gives C3*d3-C2*d2+(C2^2/(4*C3))*d1>=0. Hence

    B_N <= m0 - [N-C2^2/(4*C3)]*d1
         = m0 - N*(5*N-13)/(8*(N-2))*d1.

Any cubic certificate B_N>=kappa*m0 therefore necessarily requires
N*d1<=8*(N-2)/(5*N-13)*(1-kappa)*m0. It cannot manufacture a surviving
slow scale from complete monotonicity. This is a constraint on THIS cubic
certificate, not a necessary condition for DIRECT macro retention: retained
slow weight can coexist with a large fast-component one-step cost. Keep
DIRECT macro retention and signed filtering co-primary; do not promote
the cubic's slope requirement to a stronger mandatory frontier field.

Decisive PAPER separation, for every N>=5: the abstract strict two-mode
response R(n)=((1/100)^n+(1-1/(4*N))^n)/2 has R(N)>=3/8 by Bernoulli,
but d1>=99/200 and the preceding slope coefficient is >=5/2, so
B_N<=-19/80. The SAME source admits y=-z/99+(100/99)*T*z, computed
endpoint cap one, killing the fast mode. Its slow-mode multiplier is
>=94/99, so the existing linear telescope (or Jensen) and checked affine
cap give R_z(N)>1/3. Both eigenvalues are strict and the two-moment Gram
determinant is positive. These are exact abstract diagnostic calculations,
NOT actual BF4 moments or a Yang--Mills counterexample. They prohibit
replacing the weaker DIRECT/filter route with the cubic's slope condition.
Do not extend Taylor orders without an actual useful moment estimate.

Actual OWN currency for a fixed centered radius-zero expression, z=T^t*x:
the existing variance/cost pins and limits below give

    B_N = (1-C2+2*C3)*V_t + (-N+2*C2-3*C3)*C_t
          +(C2-2*C3)*V_(t+1) - C3*C_(t+1).

This is a signed combination of the TWO original chronological variance/cost
pairs, not a common finite-filter Gram matrix. A finite-stage test uses
their literal rational values with their OWN moving center and distinct
Z0,Z1 masses; a strict finite excess needs its actual joint/center error
certificate before passing to the completion. An already-smoothed family
still needs its full double orbit, not this two-pair substitution. Merely
computing the large signed coefficients does not estimate their cancellation.

Decision/budget: one bounded Sol leaf, <=300 lines (revise at >350), complete
independent FINAL-source review, at most three serialized root-owned focused
checks under the unchanged one-worker/20-GiB/12-GiB-reserve policy and fresh
process/memory/swap preflights. No root/tree build/audit, option increase,
spectral measure, source inverse, new analytic premise or frontier change.
Abandon/revise if a broad missing foundation or source replacement is needed.
The selection above was not kernel evidence. NEXT remains an actual ORIGINAL
relative estimate on a justified changing family, not conditional wrappers.
Canonical displayed claims unchanged.

Observed verification: `lean/YMGap/Continuum/BF4WilsonAllNomeCubicResponseLower.lean:207`,
`cubicLower`, and `:213`, `cubic_response_lower`, now supply the selected
unconditional ORIGINAL cubic lower bound. FINAL 222-line source was completely
reread by root and independently by Sol; complete FINAL-source review PASS.
Only this leaf was checked, with one worker, hard 20 GiB, 12-GiB OS reserve,
and fresh process/memory/swap preflight at EACH launch. No competing worker,
reported memory headroom 87%, swap zero; existing automatic telemetry retained.
Successful check 3 completed in its initial call (exit zero), log
`/private/tmp/ym-oct8-cubic-response3.log`, SHA256
`70f5007e6e681ebe8db2900d710ef2a2356e33b2cbd6fffe78e78d2ec3ddea12`.
FINAL source SHA256
`b69b64f8ef7f4988648b756e97f2c19027758f1240ff741144e362809ce833d5`.
BOTH public gates exactly {propext,Quot.sound}. Checks 1--2 were local
elaboration diagnostics (missing direct scalar import, case indentation,
explicit zero/one coefficient recoding), NOT proof evidence; their generated
sorryAx was not introduced into source. No new hole/axiom, source substitution,
resource-option increase or conditional analytic input. Root import registered
only; no root/full-tree build/audit/guard/metric. The quantitative margin,
PAPER limitation/separation and changing-family joins are not thereby proved.
Decision: retain this finite four-moment tool, return MAIN work to the actual
signed relative estimate or DIRECT retention; do not build another Taylor or
conditional-norm wrapper. Continuum/physical/QFT/every-group/Clay stay OPEN.
No canonical displayed claim changed; no chart reprint.

## Signed affine filters as witnesses for the ORIGINAL source (2026-10-08 UTC)

New unconditional bound KERNEL-CHECKED in the focused second check;
complete independent FINAL-source review PASS. On the ACTUAL completed
carrier put y=a*z+b*T*z and R_z(n)=B(z,T^n*z). The exact identity is

    K*R_z(n)-R_y(n)
      = (K-a^2)*(R_z(n)-R_z(n+1))
        +(K-(a+b)^2)*R_z(n+1)
        +b^2*(R_z(n+1)-R_z(n+2)).

Thus the literal computed K=max(a^2,(a+b)^2) pays EVERY-lag domination,
including n=0, vacuum and time-kernel components. No spectral measure,
source inverse or absolute cross-term bound is used. Checked declarations:
`lean/YMGap/Continuum/BF4WilsonAllNomeSignedAffineFilterBound.lean:60`,
`affine_response_expand`; `:95`, `affine_chord_remainder`; `:143`,
`affine_response_le`; `:159`, `affineEndpointCap`; `:162`,
`affine_response_le_endpointMax`. The three signs are supplied by
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectMoments.lean:343`,
`mixedMoment_nonnegative`.

PAPER consumer, independently screened; no new conditional compiler selected:
write Q=R_y(0), H=R_y(1), 0<r<1. If a rational delta>0 satisfies
delta<=H-r*Q, then Q>=delta/(1-r) and r*Q<=H. The existing
`lean/YMGap/Continuum/BF4WilsonAllNomeOddResponseJensen.lean:272`,
`response_odd_jensen`, and the selected domination give

    r^N*delta <= (1-r)*K*R_z(N).

Consequently the quantitative relative margin
r^N*delta>=(1-r)*K*kappa*R_z(0) suffices for the ORIGINAL ratio
kappa*R_z(0)<=R_z(N). It is NOT supplied by a positive filtered norm alone.
For z=T^t*x this is exactly kappa*R_x(2*t)<=R_x(2*t+N), by
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:158`,
`completedInner_time_sum`; 2*t=N=side gives the original macro target.
No different observable, earlier-source overlap or continuum limit is inferred.

For growing N, do not compute an enormous rational power merely to set the
search threshold. If N=L*k and L*(1-r)<=d<1, the EXISTING
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSmoothedTrajectory.lean:153`,
`block_bernoulli_pow`, gives nu=(1-d)^k<=r^N. The sufficient test may use
nu*delta>=(1-r)*K*kappa*R_z(0) with fixed k instead. This is a lower-bound
substitution, not a rate or physical-clock identification.

PAPER bounded search: normalize rational filter endpoints u=a, v=a+b to
|u|,|v|<=1, so K<=1. For m_i=R_z(i) the signed margin is

    S00*u^2+2*S01*u*v+S11*v^2,
    S00=m3-(2+r)*m2+(1+2*r)*m1-r*m0,
    S01=(1+r)*m2-m3-r*m1,
    S11=m3-r*m2.

A supplied positive rational-coefficient candidate can be scaled to an
endpoint boundary; simultaneous sign reversal leaves its margin unchanged.
Thus search the TWO edge quadratics (u,v)=(1,q),(q,1), -1<=q<=1,
not an unlocated eigenvector. Once four RATIONAL moment approximations are
supplied, each edge's maximum occurs at q=+/-1 or its feasible stationary
point when its quadratic coefficient is negative: -S01/S11 for the first
edge, -S01/S00 for the second, using the rational approximated S entries.
At most SIX listed candidates (duplicates harmless), no grid or CReal sign
decision. These are rational signed-coefficient choices, not source inverses.
Rational approximation must retain a strict
quantitative excess above the relative target, not merely a determinant sign.
For moment error <=epsilon, 0<r<1 and 0<kappa<=1, the normalized test
r^N*(H-r*Q)-(1-r)*kappa*m0 has error <=19*epsilon. This PAPER bound
is coefficient arithmetic, not a proved tolerance for any actual computed
moment. Reuse Type-valued `centeredTimeMomentCauchy:46` below; do not extract
data from Prop-valued convergence or infer changing-family uniformity.

For a fixed CENTERED radius-zero expression the existing two OWN variance/
cost limit pairs below supply the four m_i at 2*t. Their same-stage rational
values retain DISTINCT chronological masses; they are not asserted to be
the norm of a common finite filter. An already box-smoothed trajectory
instead retains the entire double orbit expansion from
`lean/YMGap/Continuum/BF4WilsonAllNomeSmoothedCoherentState.lean:341`,
`smoothedResponse_pin`, not just two unfiltered OWN pairs. The changing-family
relative signed margin remains OPEN. This bound is a source-preserving
quantitative tool, not a new spectral/physical/continuum/Clay closure.

For same-stage OWN scalars V=V_(stage,t), C=C_(stage,t), W=V_(stage,t+1),
D=C_(stage,t+1), the PAPER candidate test with endpoint cap one is

    nu*[a^2*((1-r)*V-C)+2*a*b*(W-r*V+r*C)
          +b^2*((1-r)*W-D)]-(1-r)*kappa*V.

Strict positivity at one finite stage is NOT enough: a supplied error
certificate must transfer its excess to the completed four-moment test.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.lean:158`,
`expressionEndpointMeanThreshold`, and `:164`, `expressionEndpointMean_approx`,
retain the moving-center control in addition to the raw joint modulus.
The available completed QCauchy datum does not automatically certify
arbitrary finite OWN-stage errors. No actual accepted candidate is produced.

Verification boundary: ONLY
`lean/YMGap/Continuum/BF4WilsonAllNomeSignedAffineFilterBound.lean`, 173 lines,
via `scripts/safe_lean_build.py --jobs 1 --reserve-gib 12
--check-worker-limit-gib 20 --check ... --check-output ...` with fresh
process/memory/swap preflights, no competing worker and zero swap. Successful
log `/private/tmp/ym-oct8-signed-affine-filter2.log`, SHA256
`77b809378265a96f6e44775d12a618242933d4fd70019f5f4ad48a1f1f691ca6`;
FINAL source SHA256
`dcb015f9c70f698e15414a4e3ec631f3e96328cc7dbb7ef33e6ab0d32e7b2492`.
Four printed theorem gates exactly {propext,Quot.sound}; the computed cap
has no axioms. Check 1's scalar-parenthesization error was repaired locally;
its failed log is diagnostic, not proof evidence. Root import registered
only; no full-root/tree build/audit/guard/metrics. No new hole, axiom,
analytic premise or resource-option increase. PAPER optimization/consumer
review also PASS; it is not a formalized or paid changing-family margin.
Canonical displayed claims unchanged; no chart reprint.

## Small signed-filter pencil: one strict margin pays its OWN norm (2026-10-08 UTC)

PAPER algebra, independently screened and root source-checked; no new Lean
closure, analytic premise or compiler/interface is introduced. For the ACTUAL
source x write m_k=B(x,T^(L+k)x), G=[[m0,m1],[m1,m2]],
H=[[m1,m2],[m2,m3]] and D=G-H. These are the existing signed-filter
quadratic forms, not new moments:
`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:195`, `orbitSum_pairing`, and
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseHankelPositivity.lean:290`,
`hausdorffSum_first_nonneg`, give the actual expansion and D nonnegativity
for rational filter coefficients.

For rational epsilon>0, u and delta>0, a produced strict signed margin

    delta <= u^T*(H-(1-epsilon)*G)*u
           = epsilon*u^T*G*u-u^T*D*u

already gives the SAME filtered norm floor delta/epsilon <= u^T*G*u.
The cleared version delta <= u^T*(c*G-s*D)*u, c>0 and s>=0,
gives delta/c <= u^T*G*u. Thus do NOT require an independent Gram
determinant/nondegeneracy estimate once this strict quantitative margin is
actually paid. This concerns the filtered state's finite completed norm,
not overlap with an earlier source or survival in a continuum limit.

For r=1-epsilon the exact two-by-two scalar test is

    det(H-r*G) = (m1*m3-m2^2)
                -r*(m0*m3-m1*m2)+r^2*(m0*m2-m1^2).

If R=H-r*G has R00<0 and det(R)<0, the symbolic vector
(-R01,R00) has signed margin R00*det(R)>0. Its entries are moment values,
NOT automatically rational filter coefficients: constructive rational
approximations must retain an explicit positive margin. No sign decision on
an arbitrary CReal or choice of an unlocated eigenvector is permitted.
For these concrete sources the available Type-valued approximation datum is
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredMoments.lean:46`,
`centeredTimeMomentCauchy`; it retains an explicit QCauchy.M. Do not extract
a numerical coefficient/modulus from the Prop-valued ConvergesTo alone.
For the following OWN substitution explicitly take
x=centeredVector(state e he), for a fixed radius-zero original expression
e with he:Within 0 e, and L=2*t. The SAME pairing pin is
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:159`,
`centeredVector_time_pairing`; an uncentered source retains a mean-square
term and does NOT satisfy this substitution. Define V_t and C_t below as
the COMPLETED limits, not same-stage finite rational quantities.
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:96`,
`originalOwnBlockVariance_pin`, `:104`, `originalOwnBlockCost_pin`, and
their `:130`, `originalOwnBlockVariance_converges`, `:143`,
`originalOwnBlockCost_converges`, give

    (m0,m1,m2,m3)=(V_t,V_t-C_t,V_(t+1),V_(t+1)-C_(t+1)).

When both unfiltered diagonal tests fail strictly, the remaining determinant
test is

    [V_(t+1)-r*(V_t-C_t)]^2
      > (C_t-epsilon*V_t)*(C_(t+1)-epsilon*V_(t+1)).

This keeps BOTH original chronological masses and moving OWN centers; no
free variance, raw Haar source norm or terminal Perron premise replaces them.
The existing macro compiler is
`lean/YMGap/Continuum/BF4WilsonAllNomeOddResponseJensen.lean:339`,
`macro_ratio_of_oneStep_block_energy`; the later-endpoint join is
`lean/YMGap/Continuum/BF4WilsonAllNomeMacroRatioFilteredCost.lean:123`,
`macro_to_filtered_budget`. Their other guards/index requirements remain.

Positivity does NOT supply the strict margin even for nondegenerate G:
the abstract two-point response m_k=((1/4)^k+(1/2)^k)/2 at L=0 has
(m0,m1,m2,m3)=(1,3/8,5/32,9/128), det(G)=1/64>0,
but every surviving filter has H/G<=1/2. At r=3/4,
R00=-3/8 and det(R)=1/512>0. This is a finite abstract diagnostic,
NOT a BF4/Yang--Mills counterexample or a new Lean certificate.

Decision: retain the four ORIGINAL moments as an optional quantitative
search, with ONE strict margin paying its OWN norm. Do not implement a
determinant/square-completion wrapper without actual changing-family signs,
explicit error margins and rational coefficients. DIRECT macro retention
remains co-primary. No such original determinant margin is produced here;
scaling, continuum/physical/QFT/every-group/Clay and chart claims stay OPEN.

## What vertex Gauss cancellation can and cannot pay (2026-10-08 UTC)

Root source inspection and independent read-only Sol screen while the actual
finite Gauss link/telescope producer is being developed. Gauge cancellation
is an independent symmetry/QFT input, not the missing quantitative estimate.
The infinitesimal slice/terminal formulas below are PAPER consequences with
their generator/embedding joins still to be built, not newly checked outputs.

The EXISTING
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularCommutation.lean:59`,
`productMap_angular_carrier`, commutes every supported in-range coordinate
plane through the literal finite product heat. It retains the full source
and explicit bounds for every selected index, allowing repeats; it does not
remove V from T=P*M_V. If the actual slice generator G and its original
embedding pins produce G(V)=0, raw Leibniz and this SAME Haar-carrier
transport would give G(T*f)=T(G*f). For invariant phi and initial constant,
G annihilates the corresponding terminal/prediction messages a,A,b,N.
The collective gauge-direction score, Ward correction and P0 then vanish.
This is a ZERO-direction identity, not a bound on the remaining individual
link/physical derivatives or a scaling-small coefficient.

Finite action invariance is not itself a new face-list mismatch:
`lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:234`,
`heatProduct_invariant`, applies to the ORIGINAL selected chronological
action after
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChainGeometry.lean:80`,
`chainIds_physical`. It still concerns the common auxiliary finite ledger,
not an already proved infinitesimal slice generator. For fringe integration,
`lean/YMGap/Continuum/SU2QuaternionHaarFamilyAngularContraction.lean:76`,
`blockAngularDerivative_familyProject`, is the existing supported transport
outside averaged blocks; averaged-block derivatives require the corresponding
independence/zero pin. No completed OS transport is inferred.

The decisive physical test is the actual spatial plaquette. Its finite
gauge invariance is produced by
`lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:208`,
`character_invariant`, on the physical slab; the literal one-slice fundamental
plaquette has full slice Casimir 12 by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCasimir.lean:141`,
`plaquette_casimir`, under every supported insertion. Do not substitute
vertex gauge cancellation for annihilation by all individual link generators.

The physical payment remains EXACTLY

    P0 = H[Vbar^2*A*T(a*(Jphi)^2)]
       = ell_V[a*(Jphi)^2*T(Vbar*A)],   A=T(a),

by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`,
`original_ratioNoise_gradientPayment_weighted_pin`. The transferred factor
is T(Vbar*Ta), NOT Ta or T^2a. A zero collective gauge derivative neither
removes this factor nor produces its relative comparison with SAME OWN
surviving variance. The retained signed interaction terms are still unpaid.

Decision: CONTINUE finite Gauss as an independent actual-source symmetry
producer; PRUNE any inference from its null directions to the missing
physical coercivity/scaling estimate. The primary producer remains DIRECT
original macro retention or sufficient JOINT signed cost versus SAME OWN
variance on a justified changing family. No canonical claim changed.

## Double-commutator localization screen (2026-10-08 UTC)

Root source inspection and two independent read-only Sol reviews. The
displayed commutator rewrites and centering calculation are PAPER algebra,
not new kernel-checked estimates. The proposed consumer is the original
relative threshold Z0*J >= (1-epsilon)*Z1*S, with BOTH OWN masses. No new
commutator/localization module is selected.

Use the actual weighted pairing <p,q>_V, actual transfer T=P*M_V,
A=T^t(g), b=T^t(g*f), u=A*f, d=b-u, Z0=<A,A>_V,
Z1=<A,T*A>_V and H_A=Z1*I-Z0*T. On supported finite polynomials set

    Q_f(A) = f^2*T(A) - 2*f*T(f*A) + T(f^2*A).

Weighted symmetry gives <A,Q_f(A)>_V=2*energy(A,f). Thus the complete
localization identity is exactly

    Z1*S-Z0*J = <A*f^2,H_A*A>_V
                 + (Z0/2)*<A,Q_f(A)>_V
                 + <d,H_A*(b+u)>_V.

Its three terms are the EXISTING boundary drift, original energy and complete
signed multiplication cost:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:204`,
`signedMultiplicationCost_difference`, and `:244`,
`original_block_rayleigh_split`. The actual two-endpoint squared-jump
identity is already produced by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:267`,
`energy_identity`. This rewrite supplies no new sign or relative bound.
It concerns finite polynomials, not a completed multiplication operator.

Although [M_f,[M_f,T]]=[M_f,[M_f,P]]*M_V algebraically, the incoming
argument remains V*A and the pairing remains V-weighted. The potential has
not disappeared. The iterated defect explicitly transfers the old defect
with V by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockMultiplicationDefect.lean:107`,
`blockMultiplicationDefect_succ`. Pointwise conversion via the existing
`BF4ExactSlabFixedSpatialCentralDensity.spatialCeiling:75` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCentralDensity.lean`
uses prefixCap(w)^(spatialFaces(width).length), not a spatially uniform cap.

Finite OWN centering also retains a signed debt. For C_A(z)=<z,H_A*z>_V,

    C_A(b-c*A) = C_A(b) - 2*c*<A,H_A*b>_V.

C_A(A)=0 is only its Rayleigh identity; it does NOT imply H_A*A=0.
The actual finite definitions of the distinct partition factors and drift
are `clearedRayleighCost:131` and `boundaryDrift:136` in the same
BlockRayleighSplit file. No finite Perron eigenvector identity is substituted.

### Existing free-energy budget and its unpaid original join

The actual free source is q=fringeProject(V*g), not g. Its exact original
energy join is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:102`,
`energy_projected_source`, under supported source/observable and the explicit
fringe-independence guards. For g=terminalMessage(n), a strictly padded
fundamental plaquette, 0<w<1, K>=2 and headCutoff(w)<=K, the EXISTING
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.lean:96`,
`padded_terminal_plaquette_energy_geometric_budget`, proves

    2*E <= 8*(1-w)*H[q^2*(4-f^2)] + 960*(1-w)^2*H[q^2].

Discarding only nonnegative H[q^2*f^2] gives the PAPER consequence
E<=(16*(1-w)+480*(1-w)^2)*H[q^2]. The stronger signed version at `:77`,
`padded_terminal_plaquette_signed_geometric_budget`, retains the actual
source-increment correction. Neither raw source moment is the interacting
centered variance. To pay the original threshold, Z0*H[q^2] still needs
a useful comparison with Z1*S, together with the boundary and signed costs.
The existing rank-one bounds
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean:197`,
`transferStepLowerCertificate`, and `:223`, `transferStepUpperCertificate`,
retain their width-dependent kinetic floor/cap; they do not supply this
changing-family relative comparison.

Sharper OWN-centered retained covariance/local radial bounds already exist:
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainCovariance.lean:321`,
`paddedSquare_own_commutatorGain_retained_covariance_bound`, and
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainRadialCost.lean:258`,
`paddedSquare_own_commutatorGain_local_radial_bound`. Their radial majorant
has r2(x)=1-4*x^3+3*x^4, x=w^(8*side), and a=w^(12*side).
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:511`,
`afSquareTransmission_lt_at_probe`, supplies cofinal actual AF probes with
a<1/8; hence x^3=a^2<1/64 and r2(x)>15/16 by PAPER arithmetic.
This is a lower floor on a MAJORANT COEFFICIENT, not on the actual signed
cost. A small relative original local source heat loss remains unproduced.
Even an optimistic absolute fixed-power payment cannot alone settle that
AF macro budget: the scalar screen
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:156`,
`afPowerBudget_no_uniform_cap`, rules out an eventual cap for every fixed
natural power side(j)*afGap(j)^p. It does not rule out signed cancellation
or constitute an original Yang--Mills counterexample.

Decision: PRUNE a redundant double-commutator/IMS wrapper. Seek a genuinely
new signed relative estimate or DIRECT macro retention on the justified
changing family. The independent actual finite gauge-source branch may
advance a backward QFT input, but does not discharge this analytic frontier.
No canonical claim or chart status changed; no new Lean check in this screen.

## Square losses and the exact late-endpoint join (2026-10-08 UTC)

Root source inspection and independent Sol mathematical screens. The new
calculations below are PAPER consequences, not newly kernel-checked estimates
or original Yang--Mills moment values. No Lean file or canonical field changes.

### Retaining the discarded squares does not supply a uniform gain

Use the ORIGINAL V,a,g,A,b,v,D,X,N,M,G of the joint-IBP section below,
and E=T(a*(Jphi)^2). H now denotes output Haar integration. Set

    Hcal = H[v^2*G^2*N*(A*J^2A-D^2)],
    P0   = H[v^2*A*E].

The exact joint-IBP identity and the existing absorption square give

    Hcal + U = P0 - Delta - Qabs - 2*Bfav,
    Delta = H[v^2*A*E*(1-(A*G)^2)],
    Qabs  = H[v^2*G^2*(N*D^2+2*A*D*M+A^3*E)],
    Bfav  = H[v^2*N*G*D*J(A*G)].

All three subtracted quantities are nonnegative by EXISTING producers:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption.lean:141`,
  private `absorption_square_pin`, identifies I_x[K*g*(D*X+A^2*Jphi)^2]
  with A*(N*D^2+2*A*D*M+A^3*E). `:195`,
  `original_ratioNoise_phiGradient_absorption_le`, reflects the sign using
  the actual positive terminal floor, without adding an inverse assumption.
- `lean/YMGap/Continuum/QuaternionHaarFiniteReciprocalHessianSign.lean:95`,
  `finite_reciprocal_favorable_certificate`, produces the sign of Bfav;
  private `derivative_four_factor_pin:130` retains it in the exact IBP
  expansion. `finite_reciprocal_hessian_ibp_le:179` discards only this
  produced favorable term, not the signed derivative of the full weight.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:267`,
  `original_ratioNoise_gradientPayment_unit_le`, produces Delta's sign
  via the multiplier-square certificate at `:305` and exact pin at `:313`.

There is a genuine, but only finite-degree, improvement. At successor degree
one G=alpha=1/upper, so Bfav=H[v^2*G^2*N*D^2]. Completing the square
3*D*X+A^2*Jphi and reflecting its sign through the same positive A gives

    Hcal + U <= (1/3)*H[v^2*G^2*A^3*E] <= (1/3)*P0.

This is not a new checked declaration. For successor degree k+1, the EXACT
derivative at
`lean/YMGap/Continuum/QuaternionHaarFiniteReciprocalHessianSign.lean:63`,
`reciprocal_multiplier_derivative_pin`, instead gives a relative favorable
coefficient beta=alpha*(k+1)*r^k/G, r=1-alpha*A. This beta is square-loss
bookkeeping, not the bare coupling. At the permitted scalar window value
A=upper/2:

    beta = (k+1)*2^(-k)/(2-2^(-k)) -> 0.

The corresponding square/Young coefficient 1/(1+2*beta) returns to one.
Thus this argument supplies no degree-uniform improvement along the
reciprocal approximation. This scalar test is NOT an actual original-action
counterexample: it does not construct a varying marginal and its derivative.
Neither Qabs nor Bfav has a produced lower fraction of the SAME surviving
OWN variance. P0 still has the exact incoming factor a*(Jphi)^2*T(v*A),
not a*(Jphi)^2*T(a) or a*(Jphi)^2*T^2(a), by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`,
`original_ratioNoise_gradientPayment_weighted_pin`. BOTH signed Taylor
remainders still belong to the original energy in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSignedScoreEnergy.lean:170`,
`exactScoreSignedBulk_energy_split`.

Decision: PRUNE another square-completion wrapper. A short finite-degree
gain is not the missing original-family cost/variance estimate.

### Direct macro retention already pays the SAME later endpoint

For R(n)=B(x,T^n*x), the EXISTING
`lean/YMGap/Continuum/BF4WilsonAllNomeMacroRatioFilteredCost.lean:100`,
`retained_time_budget`, and `:123`, `macro_to_filtered_budget`, prove

    kappa*R(L) <= R(L+s)
      => kappa*s*(R(L+s)-R(L+s+1)) <= (1-kappa)*R(L+s),

for s>=1 and kappa>=0, without a norm inverse. `:139`,
`dyadicUnit_macro_filtered_budget`, specializes the actual unit response
at lags 2*t and 4*t. The later drop at 4*t has ORIGINAL block parameter
2*t, NOT t. Do not rebuild this join or silently shift the changing-family
index: its nome, width and source need not be unchanged.

This is not shifted H1 at the EARLIER endpoint:
`lean/YMGap/Continuum/BF4WilsonAllNomeShiftedH1Anchor.lean:396`,
`PathShiftedEpsBound`, and `:418`, `pathShiftedEpsBound_iff_response`,
require s*(R(s)-R(s+1))<=c*R(s) on T^(s/2)*x. The macro-derived estimate
controls T^s*x and the drop at 2*s. Direct macro retention already feeds
`lean/YMGap/Continuum/BF4WilsonAllNomeGenericNormalizedAnchor.lean:256`,
`NormalizedAnchorData.MacroRatio`, `block_floor:325`, `real_increment:416`
and `real_floor:450`; it need not pass the stronger earlier-endpoint test.

For the optional actual two-term filter z=T^t*(a*x+b*T*x), s=2*t,
`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:195`,
`orbitSum_pairing`, gives the four-moment matrices

    Gm = [[m_s,m_(s+1)], [m_(s+1),m_(s+2)]],
    Hm = [[m_(s+1),m_(s+2)], [m_(s+2),m_(s+3)]],
    m_n = B(x,T^n*x).

A useful filter must produce its actual coefficients u=(a,b), a positive
rational q<=u^T*Gm*u, and the quantitative inequality
s*u^T*(Gm-Hm)*u<=c*u^T*Gm*u. Positivity of Gm and Hm does not supply
that threshold or a positive norm for a signed filter. For x the CENTERED
completion state of a fixed radius-zero WindowExpression e with Within 0 e,
all four moments are accessible from the two OWN variance/cost pairs at block
parameters t and t+1. The SAME completed-vector identification is
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:159`,
`centeredVector_time_pairing`; the source moment limits are
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:130`,
`originalOwnBlockVariance_converges`, and `:143`,
`originalOwnBlockCost_converges`, identify m_(2t)=V_t and
m_(2t+1)=V_t-C_t in their limits. Distinct chronological masses and moving
OWN centers stay in these producers. This two-pair claim does NOT cover an
arbitrary completed x or an already-smoothed x. A finite smoothed source
requires its orbit expansion and the corresponding additional source moments.
No new useful values or quantitative four-moment threshold are produced.

Decision: REUSE the exact late-endpoint and moment APIs. DIRECT original
macro retention or sufficient JOINT whole-window cost versus SAME surviving
variance on a justified changing family remains the unpaid analytic producer.
The bounded selected-link Ward/Casimir test is recorded next. No displayed
chart claim changes.

## Two-time local loop equation: signed debt and action mismatch (2026-10-08 UTC)

Selected experiment: combine the existing selected-link Ward identity and
degree-one Casimir with a second-time polynomial insertion. Actual consumer
would be the chronological OWN cost/variance or DIRECT macro retention,
not a static expectation. Available inputs are only the full-slab Ward,
its actual incident/complement partition and the arbitrary-insertion Casimir.
Stop if the resulting equation leaves an unestimated signed moment or needs
an unproved change of action. Budget: bounded source inspection and paper
algebra by root/Sol; no compiler, new interface or numerical sweep.

For THIS experiment only, A is the complete incident heat product and R
its complete complement in the selected-link head-swap frame. These are NOT
the terminal A and fringe v used above. Let C be supported and degree one
in that selected in-range link, h a supported second-time insertion, and
Gamma(p,q)=sum_(i<j<4)(D_ij p)*(D_ij q). Applying
`lean/YMGap/Continuum/BF4ExactSlabLocalHaarWard.lean:85`,
`fullAction_local_ward`, to h*D_ij C and summing six planes gives the PAPER
identity

    3*H[R*A*C*h] = H[R*h*Gamma(A,C)] + H[R*A*Gamma(C,h)].

The eigenvalue comes from
`lean/YMGap/Continuum/SU2QuaternionBlockLinearCasimir.lean:39`,
`blockCasimir_linear`. Exact degree one is an essential guard; do not
infer it for an arbitrary loop with repeated selected-link occurrences.
For a proved link-disjoint h, Gamma(C,h)=0, leaving
3*H[R*A*C*h]=H[R*h*Gamma(A,C)]. The right side is an UNESTIMATED SIGNED
two-time moment, not a lower floor. For a rational OWN center c, replacing
C by C-c adds -3*c*H[R*A*h] to the right; dropping it requires a proved
SAME-law zero mean of h. Ordinary Cauchy--Schwarz bounds a magnitude above,
not the required relative retention below.

There is also a decisive action guard. The actual full-slab numerator pin is
`lean/YMGap/Continuum/BF4ExactSlabLocalHaarWard.lean:55`,
`fullAction_pair_pin`, using ALL slabPhysicalFaceEdges extent. But
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChainAction.lean:45`,
`originalChainAction`, uses the selected chainIds extent width start steps.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.lean:117`,
`originalWindowScalar`, retains this clipped chronological action on extent
width+(m+(L+n)); its `originalWindowScalar_pin:123` joins that action to the
existing windowRatio. These definitions do not identify the full-slab and
chain face lists. The full-slab equation is therefore not an established
current-window Ward instance. No matching public chain-Ward instance was
found in LocalHaarWard, OriginalWardLocality, FixedSpatialChainAction or
FixedSpatialWilsonWindowTimeLimit. This bounded search does not rule out
using generic Ward algebra after producing the actual action/locality pins.

Existing consumers retain the same debts rather than supply retention:
`lean/YMGap/Continuum/BF4ExactSlabLocalHaarWard.lean:106`,
`fullAction_score_identity`, includes an extra local A in its density;
`lean/YMGap/Continuum/BF4ExactSlabOriginalWardLocality.lean:121`,
`originalScore_pair_zero_of_local`, cancels a constructed score, not C's
correlation. On the active marginal route,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:144`,
`family_normalized_ward`, already retains the signed complete-weight residual.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyRelativeWard.lean:215`,
`family_angular_variance_cleared`, bounds static angular energy;
`padded_family_energy_relative_ward:332` still retains the signed remainder.

For the actual chronological finite Rayleigh test, write
S=ell(b^2), J=ell(b*T(b)), Z0=ell(A^2), Z1=ell(A*T(A)), now using the
ORIGINAL terminal A and source b. The defining cost is Z1*S-Z0*J:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131`,
`clearedRayleighCost`. With both masses positive, a relative normalized
cost C_t<=epsilon*V_t is equivalent by ordinary rational algebra to
Z0*J>=(1-epsilon)*Z1*S, using
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:84`,
`originalOwnBlockVariance`, and `originalOwnBlockCost:89`. The loop equation
above produces neither that signed threshold nor its normalization join.

Observed decision: PRUNE a local-loop/chain-Ward wrapper absent quantitative
leverage on this actual threshold. One-link SO4 rotation is not the vertex
gauge generator. Continue with the ORIGINAL macro moments or sufficient
JOINT whole-window signed estimate on a justified changing family. This
source/paper screen closes no proof node and changes no canonical field.

Verification boundary for these two screens: independent FINAL-source
mathematical review PASS after the explicit radius-zero qualification was
added. Source declarations were inspected, not recompiled. Documentation-only
increment; no Lean file, sorry, axiom, source/action or frontier type changes,
and no root/tree build or full audit. Existing diagram claims stay unchanged.

## Joint endpoint IBP screen: centered cancellation, no new estimate (2026-10-08 UTC)

Root source inspection and independent Sol mathematical review; the formula
below is a PAPER derivation using existing producers, not a new checked
declaration or signed relative bound. Selected experiment: combine the two
retained Ward responses before estimating either absolutely. Stop if the
result is exactly an already available correction rather than a smaller
analytic input.

Let V be the ORIGINAL spatial weight, a its actual terminal message,
g=V*a, A=T(a), b=T(a*phi), v the ORIGINAL spatial fringe mass, D=JA,
X=A(y)*phi(x)-b(y), N the matched noise, and
M=I_x[K*g*X*Jphi]. G is the actual successor polynomial reciprocal, not
an assumed exact inverse. All output factors are lifted to the second
endpoint. Write L=J_x+J_y, and H for joint Haar integration. The two retained
responses combine as

    U = density + 2*spatial
      = H[K*G(y)^2*D(y)*X^2 * L(g(x)*v(y)^2)]
      = -H[K*g(x)*v(y)^2 * L(G(y)^2*D(y)*X^2)].

The actual kinetic identity L(K)=0 is ALREADY supplied by
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularForm.lean:64`,
`productHeat_pairedAngular_carrier`, including every selected factor and
repeated index. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticMarginals.lean:118`,
`kineticWeight_eq_indexedProduct`, pins literal K. Signed joint IBP uses
`lean/YMGap/Continuum/SU2QuaternionHaarAngularIBPAt.lean:120`,
`angular_pair_at`; both endpoint indices remain in range.

There IS a genuine centered cancellation: I_x[K*g*X]=0 removes the pure
output score term. Equivalently use LX=D*phi+A*Jphi-Jb directly;
I_x[K*g*X^2]=A*N and I_x[K*g*X*phi]=N. Expansion gives

    U = -H_y[v^2 * (
          A*G^2*N*J^2A + 2*G^2*N*D^2
          + 2*A*G*(JG)*D*N + 2*A*G^2*D*M)].

These are precisely the terms in the EXISTING combined Ward correction,
not a new sign-producing join. See
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:74`,
`ratioNoiseDensityMoment`, and private `hcorr:238` inside
`original_ratioNoise_ward_absorption_le:132`. In particular, centering
removes the pure score, but leaves the mixed gradient, reciprocal derivative
and marginal Hessian together; no useful sign or scaling smallness follows
from kinetic invariance alone.

The positive gradient pullback STILL has incoming weight
V*a*T(v*T(a)), not V*a*T(a) or V*a*T^2(a): same module `:384`,
`original_ratioNoise_gradientPayment_weighted_pin`. Constant/zero phi gives
X=N=U=0; constant a does not remove J(V*a). The finite closed-Wilson
vertex-gauge property in the parallel QFT audit is not this one-link paired
SO4 generator and does not supply a collective Gauss-Ward estimate.

Decision: PRUNE another joint-identity leaf; retain U as a combined signed
debt in the existing consumer. DIRECT original macroscopic response
retention or sufficient JOINT whole-window cost/OWN-variance control on a
justified changing family remains unpaid. Sharper local all-nome curvature
and its original-prefix transport are already available; do not rebuild
them or present a selected positive cap as a lower bound on actual signed
cost. No canonical field, source/action, frontier claim or chart changes.

## Direct retention need not pay the sufficient window test (2026-10-08 UTC)

Root calculation and independent mathematical review; NO Lean edits,
compiler run, new YM moment, analytic producer or canonical closure.
The user lattice-measurement note was already reconciled in
`RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`; use its SAME-theory
correlation/clock distinction, not its fitted numerical mass as a premise.

Decision experiment: test whether a DIRECT macroscopic response floor can
be made to pass the factor-two signed-window budget using positivity alone.
The existing consumer is
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`,
`normalizedAnchorResponse_block_floor`; it accepts the direct ratio without
the budget in `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`. Reject any proposed mandatory budget join
if a strictly gapped vacuum-complement example separates the two. Budget:
hand algebra plus three tiny exact rational tests, no Haar expansion/build.

For EVERY integer u>=1 take lambda=1/100, mu=1-1/(4u),
T=diag(1,mu,lambda), vacuum=e0 and x=(0,lambda^u,mu^u). Its ordinary
Euclidean pairing gives

    R(n)=lambda^(2u)*mu^n + mu^(2u)*lambda^n,
    R(2u)=2*(lambda*mu)^(2u)>0,
    R(4u)/R(2u)=(mu^(2u)+lambda^(2u))/2 >= 1/4.

Here 0<lambda<mu<1: even the vacuum complement is strictly gapped at
each u. Bernoulli gives mu^(2u)>=1/2. With C the SAME response's even-lag
drop sum over t=u,...,2u-1, elementary geometric summation yields

    2*C/R(2u)
      = (1-mu^(2u))/(1+mu) + (1-lambda^(2u))/(1+lambda).

The first term is (1-mu)*sum_{j<u}mu^(2j), at least
u*(1-mu)*mu^(2u-2)>=1/8. The second is at least its first summand
1-lambda=99/100. Therefore the factor-two window reserve
1-2*C/R(2u)<=-23/200: it fails even kappa=0 while the direct macro
reserve is >=1/4. `computations/window_reserve_two_mode_screen.py` checks
these exact identities/bounds at u=1,8,64; finite Fraction assertions are
NOT kernel proofs. The all-u argument above is not newly formalized.
This is NOT a BF4 counterexample or continuum survival: indeed
R(2u)/R(0)<=2*lambda^(2u) tends to zero. No lower/upper physical-gap
claim for the original theory is inferred.

Endpoint-error review supplies no alternative analytic payment. Writing
delta_n=R(n)-R(n+1), mixed-moment telescoping gives
sum_{t=u}^{2u-1}m(2t,2)<=delta_(2u)-delta_(4u) and
2u*delta_(2u)<=R(0)-R(2u). The latter is a direct specialization of
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:71`,
`mixedMoment_time_budget`. An absolute same-source floor R(2u)>=eta*R(0)
would control that error, but
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedLogConvexity.lean:133`,
`macro_ratio_of_survival_floor`, already consumes the floor more directly.
Likewise the earlier SAME-source block floor is already consumed by
`lean/YMGap/Continuum/BF4WilsonAllNomeBlockResponseLower.lean:104`,
`response_shifted_block_step_lower`. Add neither endpoint wrapper nor an
unnecessary absolute-norm prerequisite to the normalized-anchor route.

Decision: retain DIRECT original macro moments as a co-primary analytic
producer; the signed-window sufficient estimate remains eligible, not
mandatory. Either route must still produce its actual original bound on a
justified changing family with its OWN centers and chronological masses.
Feasible exact-moment evaluation remains unpaid; the compression source map
is appended to `AUDIT-ORIGINAL-MOMENT-PILOT-FEASIBILITY-2026-09-30.md`.
No interface, hypothesis, frontier field or chart statement changes.

## Scalar/symmetric retention decision after the filter reduction (2026-10-08 UTC)

Root source inspection and two independent read-only mathematical screens.
This section supplies NO new interacting estimate or kernel-checked survival
theorem. The parallel boundary-list certificate is recorded in the QFT-inputs
audit; it does not pay the signed cost below.

For the OWN-centered symmetric origin sum S=chi01+chi02+chi12, existing
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:151`,
`familyExcitation_norm_floor`, gives R_S(0)>=3*varianceFloor(w) at fixed
strict nome and positive width. Its moments are not determined by the
antisymmetric x: source-level permutation algebra gives R_S(n)=3D_n+6O_n
and R_x(n)=2D_n-2O_n, where D/O are centered diagonal/off-diagonal face
responses. S keeps its moving OWN mean; do not impose the odd source's zero
mean on it. A sharper symmetric moment estimate remains NOT PRODUCED.

At padded width>=2, an ACTUAL existing Rayleigh floor is available:
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:104`,
`family_rayleigh_floor`, using
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:165`,
`familyResponseFraction`, and `:243`, `padded_family_energy_band`.
For three faces rho3=w^12*localLower(w,12)^2/localUpper(w,12)^2, with the
positive reciprocal explicitly constructed in that declaration. But
`lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:64`,
`familyResponseFraction_le_ceiling`, bounds THIS supplied floor by 2^(-840).
Its corresponding cost coefficient is therefore >=1-2^(-840), independent
of how close nome is to one. This is a limitation of the existing bound,
NOT a bound above on the actual Rayleigh quotient. Do not increase family
size merely to reuse this band. Width one is an actual fringe test:
`lean/YMGap/Continuum/BF4ExactSlabWidthOneGeometry.lean:75`,
`activeSpatialFaces_one`, and
`lean/YMGap/Continuum/BF4WilsonAllNomeFringeTimeKernel.lean:59`,
`inactive_face_time_one_zero`, kill each centered origin face. Bilinearity
therefore gives R_S(1)=0 for their sum (source-level consequence, NOT a new
symmetric-source theorem). This rules out that width, not padded sources.

The optional single filtered-slope seed
2*u*(R_x(2u)-R_x(2u+1))<=theta*R_x(2u), theta<1, would suffice for
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`, by decreasing response drops. It is NOT
minimal or necessary. Exact scalar test, not a YM moment/eigenvector:
u=8, rho=7/8, R(n)=rho^n. Then the seed's left/right relative factor is 2,
but the aggregate window leaves positive margin

    (16*rho^16-1)/15 = 250251912402960/4222124650659840 > 0.

Thus a direct whole-window certificate can succeed where that convenient
one-slope prerequisite fails. Keep DIRECT aggregate/block retention as the
weaker main target; no new slope interface or stronger initial criterion.
Actual original finite ingredients remain
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:96`,
`originalOwnBlockVariance_pin`, and `:104`, `originalOwnBlockCost_pin`:
distinct Z0,Z1, moving OWN center and the COMPLETE signed cost. Neither
scalar-filter monotonicity nor a symmetric-source floor estimates these
quantities on a justified changing family. NEXT remains their original
interacting producer, not another source/symmetry/conditional wrapper.

## Selected independent-filter reduction and spatial-profile decision (2026-10-08 UTC)

Previous goal turn: PROGRESS, commit `81dbc973` supplies the actual common-
filter orbit identity. The remaining independent-filter branch is screened
by a stronger exact consequence, not by a new spectral or survival premise.

Write P(x)=orbitSum(x,cs), Q(x)=orbitSum(x,ds), for arbitrary finite signed
rational coefficients and natural time lags. On the EXISTING original
Wilson completion, strict nome and width>=1, select the proposition

    4*R_(P(x)+Q(y))(n) = R_(2P(x)-Q(x))(n) + 3*R_(Q(x))(n).

The SAME equality is sought for each forward lag difference R(n)-R(n+1).
Predicted outcome: the two-orientation finite Hankel/Krylov calculation
reduces to two scalar-filter responses of x; no additional orientation
overlap or independent temporal moment sequence is obtained. This does NOT
say scalar filtering cannot improve retention or produce a slow rate.
The elementary argument uses z=x+2y: every-lag B(x,T^n z)=0 and R_z=3R_x.
No norm inverse, nonzero filter, time-invariant local span or spectral
existence assertion is needed.

Inputs: `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:331`,
`mixed_response`, and `:340`, `diagonal_response`;
`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:166`, `orbitSum`,
and `:195`, `orbitSum_pairing`. The existing original-cost limits remain
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:130`,
`originalOwnBlockVariance_converges`, and `:143`,
`originalOwnBlockCost_converges`. Consumer: the actual filtered variational
screen, ultimately the signed relative budget at
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`. This reduction supplies no such budget.

Decisive tests: unequal filter lists and lags, arbitrary negative and zero
coefficients, empty filters, n=0 and width1 time-kernel components. Budget:
one bounded Sol leaf, independent final-source review, one serialized
20-GiB focused check with fresh dynamic preflight and 12-GiB host reserve.
Revise/stop if a new symmetry, analytic bound, carrier or spectral theorem
is required. Selection is not yet a kernel-checked result.

### Observed independent-filter proof (2026-10-08 UTC)

The selected response and cost-difference identities now PASS one final
focused Lean check; independent final complete-source mathematical review
passes. Arbitrary independent signed filter lists, repeated or empty lists,
zero/null directions, n=0 and width1 remain in scope. All objects are the
EXISTING original Wilson completion and its actual completed time.

| Produced result | Exact source |
| --- | --- |
| Every mixed lag of two independently filtered y directions equals its x counterpart | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteKrylovReduction.lean:77`, `filtered_diagonal_response` |
| Signed mixed-filter response, with factor TWO cleared before the finite sums | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteKrylovReduction.lean:89`, `filtered_mixed_response` |
| 4*R_(P(x)+Q(y))=R_(2P(x)-Q(x))+3*R_(Q(x)) at every lag | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteKrylovReduction.lean:159`, `independent_filters_response` |
| Identical 4/1/3 decomposition of forward lag differences | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteKrylovReduction.lean:210`, `independent_filters_forward_cost` |

Decision: reduce this two-orientation finite-filter search to the SAME
scalar moments R_x(n+i+j). Scalar filtering remains eligible and may change
retention; no useful moments, slow rate or overlap bound is produced here.
Different sites and the centered symmetric sector are NOT reduced to x.
The completed cost identity does not identify distinct finite chronological
partitions or authorize iterating a row-normalized finite transfer. Any
finite moment certificate must still retain its original window, OWN mean
and both masses; the radius-zero original-cost API is not asserted to be a
general finite mixed-filter realization. No new carrier/filter/interface,
variance inverse, nonzero premise or spectral theorem is introduced.

Verification: all four printed gates exactly {propext, Quot.sound}, no
sorryAx or warning in the final log. One serialized 20-GiB worker, 12-GiB
host reserve, fresh dynamic-capacity preflight before each launch. The first
check's one scalar-distribution rewrite error and its generated sorryAx
output are NOT evidence. The only repair distributes two explicit scales
using the existing RCscale_RCadd; no proposition or limit changed. Root
read the complete final source. Root import registered only; no root/tree
audit, guard, new hole/axiom, classical/native shortcut, canonical field or
chart closure. The whole Clay target and actual signed scaling input remain
OPEN. No broad discharge count is inferred.

Accepted log and SHA-256:

```text
/private/tmp/ym-origin-krylov-reduction-20261008b.log
  e4c5d82e78888236c1cfacf896691cbcb2b07a059ee653a787801dbb866961a0
```

Checked source SHA-256:

```text
81561d7aba782e486105a4f19f1cc82d75f4531bdf036469baa69498a73bfb49
```

### Spatial coefficient cancellation: source-backed screen, NOT a new proof

Root inspected the cited declarations; independent mathematical review
agrees. Actual rows use quaternion-tail correlations:

    Gamma_l(F) = 4*||sum_(p incident l) c_p*tau_lp||^2 - F_l^2.

Source: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentTail.lean:183`,
`actual_face_tail_recode`, and `:383`, `family_coherent_row`. The complete
original energy already retains these squares and BOTH Taylor debts in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:263`,
`family_coherent_energy_retained_square`. A scalar coefficient difference
does not identify the difference of these field-dependent ordered tails.

Exact paper test on actual adjacent words, not a new checked witness:
width>=2, shared link ((1,0,0,0),x1)=1; links ((0,0,0,0),x0)=i and
((1,0,0,0),x0)=-i; every other link=1. All values are rational unit
quaternions. With variable shared U, the two traces are chi(U*i)=-2U_i and
chi((-i)*U^-1)=-2U_i. At U=1, equal coefficients have shared angular square
16 and complete angular square 40, while opposite coefficients have shared
square 0 and complete square 24. Replacing -i by +i exchanges these cases.
Sources: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentAngularCancellation.lean:184`,
`original_adjacent_trace_pins`; and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentFullAngular.lean:425`,
`adjacent_full_angular`. This rejects a universal PER-SHARED-ROW
coefficient-difference-only bound; it does not refute a global estimate with
separately paid true boundary rows or an estimate under the interacting law.
At this boundary row the incident spatial action remains
V_nonincident*h(-U_i)^2*h(U_0), h=the original heat prefix. The terminal
messages and all remaining action factors still belong to the original law.
No action or interacting moment is replaced by this pointwise paper test.

First-order source derivatives already cancel in
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularTaylor.lean:91`,
`sourceFirstOrder_eq_weightedAngularEnergy`; the higher signed terms remain.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`,
`padded_family_energy_variance`, retains 12*(1-w)*OWN variance plus the
complete signed correction, not an extra power from coefficient smoothness.
The concrete filtered target remains D<=epsilon*Z1*ell_V(b^2), with
D=Z0*E(A,phi)+boundaryDrift+signedMultiplicationCost and BOTH actual
chronological partitions. Its identity, not its estimate, is proved at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:214`,
`clearedRayleighCost_split`.

Decision: retain different sites and the centered symmetric sector as
genuine sources of NEW interacting moments; do not implement another
coefficient-gradient, Ward-cancellation or conditional matrix wrapper.
Work still requires an actual interacting correlation/signed-response
estimate and justified changing-family control. No broad chart claim closes.

## Selected actual three-face orbit response test (2026-10-08 UTC)

Proposition: on the EXISTING original Wilson completion at strict nome and
width>=1, set x=chi01-chi02 and y=chi02-chi12 for the three literal origin
spatial fundamental plaquettes. Prove, for every actual completed lag n,

    B(y,T^n y) = B(x,T^n x),
    2*B(x,T^n y) = -B(x,T^n x),
    B(a*x+b*y,T^n(a*x+b*y)) = (a^2-a*b+b^2)*B(x,T^n x).

Predicted consequence: no coefficient optimization in this TWO-dimensional
zero-sum origin-face orbit improves its normalized temporal response, including after
the SAME common actual time filter T^u. Independently filtered basis vectors,
other sites and higher spins are not excluded. The division-free identity covers degenerate/null
filtered directions; no norm inverse or transfer-invariance of this local
span is needed. This is an obstruction to a specific variational search,
not a bound on the response or a refutation of larger spatial profiles.

Available inputs: the actual U01/U12 pairing-preserving completed swaps and
their completed-time commutation, in
`lean/YMGap/Continuum/BF4WilsonAllNomeSpatialHeadSwapCompletion.lean:176`,
`completedSwap_time`, and `:231`, `completedInner_swap`, and
`lean/YMGap/Continuum/BF4WilsonAllNomeSpatialAxisSwapCompletion.lean:70`,
`completedSwap_time`, and `:125`, `completedInner_swap`. Ordered reversed
face characters must be pinned by quaternion conjugation, not factor
commutation. Produce the literal source relations before using bilinearity:
U12*x=-x, U12*y=x+y, U01*x=x+y, U01*y=-y.

Consumer: the filtered Galerkin screen below. A matrix formed only from this
orbit with a common filter cannot produce a better chosen-source retention
via a maximum Ritz direction. Selected derivative/action insertions do not satisfy these pins
without transformation of their own indices and weights. Keep their full
signed costs; do not erase them by oddness.

Decisive tests: width0 excluded; width1/null directions permitted where the
stated type allows; arbitrary signed a,b, n=0 and changing coefficients;
all three literal ordered faces, physical x3 time and SAME normalization.
Budget: one bounded Sol leaf, independent complete-source review, root-only
20-GiB focused check after fresh dynamic preflight, 12-GiB OS reserve. Stop if
an assumed symmetry, new carrier or missing analytic input is required.
No new matrix interface or scaling hypothesis is selected. Observed results
will be recorded separately; this selection itself is not a checked proof.

### Observed original three-face response proof (2026-10-08 UTC)

The selected proposition is now kernel-checked on the actual original
completion; independent final complete-source mathematical review PASS.
Write R_x(n)=B(x,T^n x). All statements below name strict nome, width>=1,
and the existing physical completed time. No symmetry, analytic-smallness
or survival premise is supplied.

| Produced result | Exact source |
| --- | --- |
| Ordered source characters, including reversed faces by scalar conjugation | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:110`, `head_sourceCharacter`; `:119`, `axis_sourceCharacter` |
| Concrete face embeds transported on SAME completion | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:156`, `head_faceVector`; `:176`, `axis_faceVector` |
| Actual U12*x=-x, U12*y=x+y, U01*x=x+y, U01*y=-y | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:214`, `axis_x`; `:220`, `axis_y`; `:227`, `head_x`; `:234`, `head_y` |
| Literal x joins EXISTING antisymmetric source, including terminal zero-fold syntax | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:241`, `x_antisymmetric` |
| Every-lag 2*B(x,T^n y)=-R_x(n), R_y(n)=R_x(n) | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:331`, `mixed_response`; `:340`, `diagonal_response`; `:354`, `mixed_response_half` |
| Arbitrary signed rational a,b: R_(a*x+b*y)(n)=(a*a-a*b+b*b)*R_x(n) | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:400`, `trial_response` |
| SAME factor after COMMON T^u; cleared response-ratio equality, including null cases | `lean/YMGap/Continuum/BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:413`, `common_time_filter_response`; `:435`, `common_time_filter_cleared_ratio` |

Decision: PRUNE coefficient-only optimization in this zero-sum origin-face
orbit under a common time filter as an improvement to normalized retention.
This does NOT show that the local span is time-invariant, produce a slow
rate, or exclude independent filters, other spatial sites, higher spins or
the centered symmetric combination. The common-filter assumption is
load-bearing. Selected derivative/action insertions still require their own
transformed indices and weights; oddness does not remove quadratic costs.
The NEXT estimate remains actual JOINT signed filtered cost/reserve versus
the SAME surviving interacting variance on a justified scaling family.

Verification: final focused check PASS, 29 printed gates (four axiom-free,
25 exactly {propext, Quot.sound}), no sorryAx or warning. One compiler,
20-GiB worker cap and 12-GiB host reserve, fresh capacity preflight before
each launch. The first two checks failed on bounded expression elaboration
and scalar syntax/distribution; their generated sorryAx output is NOT
evidence. Final repairs changed no proposition or premise and raised no
limits. Root read the final source; independent review passes. Root import
registered only; no full-root/tree build, guard, new hole/axiom, classical/
native shortcut, canonical field or chart change. The legacy progress metric
was not run because it invokes an unauthorized guard build.

Accepted log and SHA-256:

```text
/private/tmp/ym-origin-orbit-response-20261008c.log
  2f8a60bac4bc14f187b77b4897fa4d307229a1692369d0014371a338695de521
```

Checked source SHA-256:

```text
27bb668b2548a7105f89138dbd39ba08b3c244b7d963f41b6897108db6d2a785
```

## Curvature orientation and filtered variational screen (2026-10-08 UTC)

Root inspection and independent read-only mathematical review. These are
DERIVATIONS from existing declarations, not new kernel-checked estimates.
No hypothesis, compiler, source or canonical frontier is added by this screen.

### Regional log-concavity does not pay the required lower curvature

For X=relativeScalar, d=D_u X, R=sum(u_i^2), the actual frozen second jet
gives

    h*D_u^2 h - (D_u h)^2 = (h*h''-h'^2)*d^2 - R*X*h*h'.

Source: `lean/YMGap/Continuum/SU2QuaternionPairedFrozenJacobiCurvature.lean:54`,
`frozenHeat_second_pin`. Scalar log-concavity and h'>=0 would therefore
give an UPPER log-Hessian sign on X>=0. The actual certificate at `:83`,
`frozen_curvature_certificate`, instead gives

    C*R*h^2 + h*D_u^2 h - (D_u h)^2 >= 0,

a LOWER bound. The upper regional sign does not lower the required C.
It also says h*dd<=d^2, not that the integrated dd is nonpositive, as
required by `lean/YMGap/Continuum/QuaternionHaarCurvatureDualBound.lean:148`,
`curvature_dual_bound`. The signed version `curvature_signed_dual_bound:180`
retains that term correctly.

The actual marginal expression retains A*D_u^2 A-(D_u A)^2+C*R*A^2:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalMarginalJets.lean:497`,
`localSignedFisher_marginal_pin`; the matched terminal consumer is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalLocalSignedGram.lean:649`,
`terminal_local_signed_score_bound`. Integrating a positive density adds
conditional score covariance to its log-Hessian. There is no produced
hemisphere restriction, southern-region payment or covariance bound here.
Moreover the Jacobi certificate is for the weighted approximant; the original
prefix lower-curvature transport does not assert a regional upper-sign pin.
**PRUNE a hemisphere-sign wrapper; it supplies no required payment.**

### Exact defect credit removes slack, not the missing rate

Write R(k)=B(x,T^k x), D=I-T, and m(k,l)=B(x,T^k D^l x). The existing
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectMoments.lean:349`,
`mixedMoment_split`, gives the exact identity

    R(2*start)-R(2*(start+count))
      = 2*sum_{j<count} m(2*(start+j),1)
        - sum_{j<count} m(2*(start+j),2).

The retained second-defect sum is nonnegative by `mixedMoment_nonnegative:343`;
at even lag each summand is ||D*T^(start+j)x||^2. Thus the factor-two window
test in `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`, is sufficient, not necessary. On a scalar
mode rho its credit is order (1-rho)^2 per step. At rho=1/4, start=count=1,
the actual macro retention is R(4)/R(2)=1/16, while twice the one-step cost
divided by R(2) is 3/2; the missing second-defect credit is 9/16. This is a
scalar test of sufficiency slack, not an original YM source or a scaling
counterexample. Fixed rho still loses every scale-independent macro floor
as the window grows. No estimate of this credit
against SAME filtered variance is supplied. A new exact-credit consumer alone
would just restate the macro-ratio obligation, so it is NOT implemented.

### A filtered Galerkin certificate is eligible, but must supply real moments

At one ORIGINAL chronological endpoint, use the literal moving OWN centers:

    v_i = T^u(g_stage*(f_i-c_i,stage))
    G_ij = ell(v_i*v_j)/Z0
    H_ij = ell(v_i*T(v_j))/Z1.

The six symmetric entries of a two-source compression can be represented
using `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:52`,
`observedMessage_endpoints`; `:88`, `block_window_numerator`; `:139`,
`normalized_block_window_pin`. The actual filtered norm/cost and their
fixed-source limits are pinned by
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:96`,
`originalOwnBlockVariance_pin`; `:104`, `originalOwnBlockCost_pin`;
`:130`, `originalOwnBlockVariance_converges`; `:143`,
`originalOwnBlockCost_converges`.

A genuine division-free sufficient certificate is the positive-semidefinite
matrix with entries

    Z0*ell(v_i*T(v_j)) - rho*Z1*ell(v_i*v_j).

It pays the chosen source only when its actual filtered numerator equals
sum(alpha_i*v_i). A maximum Ritz value alone gives a slow trial, NOT overlap
with the designated source. Rank one is precisely the missing filtered cost
estimate. A direct macro matrix B(v_i,T^(2u)v_j)-kappa*B(v_i,v_j) bypasses
the sufficient-only factor-two test, but its chosen-source quadratic bound
is the still-unpaid macro retention. Do not iterate (Z0/Z1)*T as if later
chronological partitions were unchanged. Zero/degenerate Gram directions
need no variance reciprocal.

The current family-band coefficients are already screened by
`lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:117`,
`family_band_coefficient_floor`, and `:139`,
`transported_family_band_coefficient_floor`; no duplicate ceiling is needed.
**Decision:** keep DIRECT filtered signed or variational control eligible,
but select no matrix interface without a concrete original-moment bound and,
where needed, quantitative source overlap. Neither this screen nor finite
spatial-symmetry work supplies survival or a scaling rate. Main work remains
the actual interacting producer, not more CS/completion/spectral wrappers.

## Remaining Gram-credit screen and route decision (2026-10-08 UTC)

Root source inspection and independent bounded mathematical reviews. The
following are algebraic DERIVATIONS from the cited declarations, not newly
kernel-checked theorems. They close no canonical proof node.

Keep the actual unfiltered source q, the literal antisymmetric f and the
full bare product heat P. Write

    lambda = w^12
    S = H[q*f^2*Pq]                 (original q*Pq marginal)
    E = S - H[q*f*P(q*f)]
    A = H[q^2*f^2]
    B = H[q^2*P(f^2)]
    C = singleEndedCost(q,f)
    I = sourceIncrementCost(q,f)
    V = 16*S - 8*E + Dplus
    X = H[W*jump(q)*jump(f)*sum(q)*sum(f)].

Both Gram means are already produced zero in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:214`,
`jump_mean_zero`, and `:226`, `sum_mean_zero`. The bare eigenpin is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`,
`spatialSpan_fullRange`; it is NOT an interacting-transfer eigenpin.

The scalar product of the two tests is jump(q^2)*jump(f^2). Applying
`lean/YMGap/Continuum/SU2QuaternionProductHeatJumpMean.lean:72`,
`jump_mean`, with squared inputs, and
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceYoungMoments.lean:92`,
`singleEndedCost_eq_moments`, gives

    X = 2*(A-B),
    C = 2*(1-lambda)*A - X/2.

`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceYoung.lean:203`,
`four_mul_sourceEnergy_add_increment_eq_two_singleEnded`, gives

    4*E + I = 2*C,
    I = 4*(1-lambda)*A - X - 4*E.

The denominator identity is
`lean/YMGap/Continuum/SU2QuaternionProductHeatSumNorm.lean:256`,
`sumTest_norm_energy_pin`. Consequently the checked budget at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:248`,
`original_energy_response_budget`,

    4*V*E + X^2 <= 2*V*C,

is exactly X^2<=V*I: Cauchy--Schwarz for the actual two tests. Cancellation
uses the displayed identity, not division by V or a source norm. It supplies
no new relative rate without a quantitative interacting-source estimate.

Decisive algebraic test: for q=1 and the centered bare eigenfunction,
A=B=S, X=I=Dplus=0, E=(1-lambda)*S, V=8*(1+lambda)*S. The budget saturates.
For the zero source every displayed quantity is zero. These are tests of
the generic inference, NOT actual BF4 terminal-source instances or a
Yang--Mills counterexample. The actual q retains spatial action and terminal
messages. In particular A uses q^2 while S uses q*Pq; they are not identified.

The one-face square image already exists at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceEvenCancellation.lean:77`,
`square_heat_moment`. It still retains an unrestricted signed q^2-weighted
spin-two moment. A shared-link image for the two-face square would compress
X into further loop moments, not estimate their sign or size. No such image
is implemented here solely to replace the missing estimate by another list.

**Decision: REVISE the Gram branch to an interacting producer, not another
CS/square-moment wrapper.** The next required output is the JOINT signed
filtered cost versus its SAME surviving variance, or an actual original
blocking comparison that produces it. The existing consumers are
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`, and the actual profile identification in
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:130`,
`originalOwnBlockVariance_converges`, and `:143`,
`originalOwnBlockCost_converges`. Direct filtered control remains eligible;
the stronger initial unfiltered Rayleigh floor is not imposed as necessary.

### Even-cost and original time-decimation checks

Antisymmetry reverses b=T^t(g*f), u=A*f and b-u. Both factors of
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:144`,
`signedMultiplicationCost`, reverse, so their pairing is EVEN. Energy,
surviving variance and `boundaryDrift:136` are even as well. No useful
quadratic sign follows from the zero means. The actual source is not
energy-null: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:174`,
`family_energy_floor`, with coefficient budget 2, gives
2*lower(w)<=600*upper(w)*normalizedEnergy. This is a finite energy lower
bound, not an upper estimate on filtered cost.

At arbitrary cutoff, original time-decimation gives

    L2(x,z) = integral K(x,y)*V(y)*K(y,z) dy,
    endpoint law = V(x)*L2(x,z)*V(z)/Z2.

Exact source: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean:61`,
`middleIntegrand`; `:73`, `gluedMiddle`; `:188`, `original_twoLayer_gluing`.
Its compression is the actual polynomial at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBoundaryCarrier.lean:173`,
`kernel`, with reconstruction `kernel_reconstructs:182`. Middle V occurs
once; neither endpoint V is erased. The bare L2 row is T1, not an asserted
unit row, by `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGluedEndpointMarginal.lean:105`,
`chronological_middle_pairing`, and `glued_lower_endpoint_pairing:169`.
Including the upper V yields row T^2(1), with the original partition at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMiddlePairing.lean:102`,
`chain_partition_pairing`.

Where the positive conditional ratios are defined, let g_d=T^d(1).
The two-step row normalization would be P2(f)=T^2(f)/g_2. Its repetition
inserts T^2(T^2(f)/g_2)/g_2, NOT the chronological four-step ratio T^4(f)/g_4
without an additional identity. In a longer unchanged original chain the
endpoint law instead retains V(x)*g_d(x)*L2(x,z)*V(z)*g_e(z)/Z_(d+e+2);
its forward conditional is T^2(g_e*f)/g_(e+2). These are derived normalized
expressions, not new polynomial operators or checked stationarity claims.
Original iteration and exterior-message pins:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalIteration.lean:182`,
`original_chain_iteration`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMiddlePairing.lean:63`,
`terminalPair_total`.

The existing actual conditional projection is on ORDINARY weighted state
GNS: `lean/YMGap/Continuum/BF4ExactSlabBlockConditionalProjection.lean:90`,
`conditionalProjection`; `:158`, `conditionalProjection_norm`. A theorem
identifying it with a map on the all-nome reflected OS carrier is NOT FOUND
in that module or the cited original gluing/marginal modules. Do not infer
an OS gap or the relative RG comparison from its norm-one bound.
Non-strict same-carrier time contraction is already available at
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:191`,
`completedInner_time_contraction`; it supplies no useful new scaling margin.

No compiler was used for these screens. No new hypothesis, stationarity
premise, canonical field, continuum claim or chart change is introduced.

## Selected antisymmetric ORIGINAL source (2026-10-08 UTC)

Proposition: for width>=1 take the literal fundamental-character difference
between origin faces p01 and p02, with coefficients +1,-1. The existing x1/x2
swap exchanges these ordered loops without reversal. Prove its finite
original chronological scalar, endpoint means and moving OWN center are
exactly rationally equivalent to zero, at every stage/depth, and exhibit
its nonzero state on the EXISTING completion with the existing two-face
variance floor. Do not merely assume an odd source or a symmetry witness.

Inputs: `SpatialAxisSwapWilsonWindow.originalWindowScalar_swap`, literal
physical plaquette loops, original finite linearity and endpoint pins,
`PlaquetteFamilySourcePin.familyExpression`, and
`PlaquetteFamilyVariance.familyExcitation_norm_floor`. Consumer: specialize
the new SAME-source OriginalRayleighLimit without moving-center debt, and
remove the completed mean-product correction for this produced source.
This is a selected-source algebraic simplification, not a slow-rate estimate.

Independent source screens predict success. Decisive tests: exclude width0,
check physical nonrepeated faces, keep all action/partition factors and source
inverse flags, and retain coefficient-square budget 2. The quadratic signed
costs are swap-even and do NOT vanish. Unrelated Gram-test means require their
own invariant-weight pin; do not erase them from odd marginal mean alone.
Budget: bounded Sol finite-source implementation, root completed/variance
consumer, independent complete-source review, serialized root-only focused
20-GiB checks with 12-GiB reserve and fresh dynamic-capacity preflight.
Stop if an existing identical producer is found or an additional analytic
premise is needed. No new norm inverse, completion, scaling input or canonical
field change is selected. Observed proof evidence is recorded separately.

Bounded follow-on decision: the actual Gram means J and M can be tested
without a new transfer-symmetry framework. The existing product-heat jump
and sum-test mean pins reduce them to H[q*f] and H[q*P(f)]. For this literal
two-face family the existing full-range heat eigenidentity gives P(f)=w^12*f.
Use the original zero mean at L=0,m=depth,n=0 and its positive chronological
partition to prove H[q*f]=0, retaining q as the projected ORIGINAL terminal
source. Strict padding from spatialFaces(1) requires width>=2 to supply
the existing fringe-independence guard; width1 nondegeneracy is not survival.
Predicted output: J=M=0 in the actual SourceVarianceGram consumer, with
the swap-even cross credit and source-jump square UNESTIMATED. Budget: one
bounded Sol leaf, root-only capped check, independent full-source review.
Stop rather than assume q invariance or replace its weight/action. This
removes actual mean corrections, not a signed scaling obligation.

### Observed antisymmetric-source proof evidence (2026-10-08 UTC)

All three selected leaves now pass focused kernel checks. Independent
complete-source mathematical reviews pass; final compiler fixes changed
only imports, namespace/notation resolution, explicit sequence annotation
and local unfolding, not any statement or premise.

| Produced result | Exact source |
| --- | --- |
| Physical distinct p01,p02, literal ordered loop exchange and coefficient-square budget 2 | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricPlaquette.lean:50`, `face01`; `:51`, `face02`; `:57`, `faces_physical`; `:69`, `coefficient_square_budget`; `:87`, `swapSourceLoop_face01` |
| Every finite ORIGINAL chronological mean is zero | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricPlaquette.lean:126`, `original_mean_zero` |
| Exact endpoint and moving OWN mean zero, literal centered source unchanged | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricPlaquette.lean:168`, `endpointMean_zero`; `:176`, `ownMean_zero`; `:191`, `shifted_source_pin` |
| Existing joint-limit/unit pairing zero; centered moments equal raw moments | `lean/YMGap/Continuum/BF4WilsonAllNomeAntisymmetricPlaquette.lean:60`, `joint_mean_zero`; `:72`, `state_mean_zero`; `:85`, `centeredMoment_uncentered` |
| Raw embed in SAME vacuum complement, squared norm >=2*varianceFloor(w)>0, SAME completed time correlator | `lean/YMGap/Continuum/BF4WilsonAllNomeAntisymmetricPlaquette.lean:100`, `excitation`; `:128`, `excitation_norm_floor`; `:136`, `excitation_norm_ne_zero`; `:159`, `excitation_correlator_pin` |
| Literal spatialSpan recoding and PRODUCED fringe independence for width>=2 | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:82`, `source_spatialSpan_pin`; `:87`, `source_fringe_independent` |
| Actual OWN-centered span is coefficient-pinned to original Wilson source | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:135`, `ownMean_spatialSpan_pin`; `:141`, `oddCentered_source_pin` |
| Separate one-sided raw mean H[V*g_depth*f]=0, then actual projected H[q*f]=0 | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:162`, `raw_endpoint_mean_zero`; `:188`, `projected_endpoint_mean_zero` |
| Both actual Gram means J=M=0 and simplified original energy budget | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAntisymmetricGram.lean:203`, `projected_heat_mean_zero`; `:214`, `jump_mean_zero`; `:226`, `sum_mean_zero`; `:248`, `original_energy_response_budget` |

Interpretation: width>=1 gives a nonzero exactly centered initial source;
width>=2 supplies the stronger fringe guard needed by the finite energy
consumer. The one-sided terminal mean is proved independently of the OWN
odd-marginal mean: no substitution between these two densities occurs.
The bare P(f)=w^12*f pin is used ONLY under the actual q insertion to remove
linear means. No interacting-transfer eigenvalue is inferred. The final
finite budget retains V=16*S-8*E+Dplus and X=H[W*r*s], giving
4*V*E+X^2<=2*V*singleEndedCost. Neither Dplus nor X is estimated here.
The source/nome/width stay fixed in the limit. No positive-time lower bound,
changing-family modulus, scaling-uniform floor or physical/Clay closure.

Verification: three successful serialized focused checks, 15+11+10=36
printed gates, each empty or within {propext, Quot.sound}, no sorryAx.
One compiler, 20-GiB cap and 12-GiB OS reserve, with fresh dynamic-capacity
preflight before each launch; swap use remained zero. The Gram check has
one harmless unused-section-variable warning on the private q_supported
helper. No full-tree/root audit or regression on unchanged machinery.
Root imports are registered only. No new hole/axiom, classical/native
shortcut, option-limit increase, canonical field or chart change.

Successful logs and SHA-256:

```text
/private/tmp/ym-antisymmetric-finite-20261008b.log
  92b0f4a746445c5ff53e5e1d54c0c96a7a51575e036a11b08390c721f83af92d
/private/tmp/ym-antisymmetric-completed-20261008b.log
  bd758ada980f2f220989df46a3e0e80d875fc7331efb78c1b41e7a0a60b21227
/private/tmp/ym-antisymmetric-gram-20261008c.log
  46d67c47ed818e00497c846f98e216968aeada609757874dcb7299c3fb265ac2
```

Checked source SHA-256, in the same finite/completed/Gram order:

```text
d1ba1be8ee93082fd970158991acded74438c727b2cb20669ec53a9cf1e6e189
715a12ec41c5b794fa90703fa6abdd324375fda650cc6bcce71269f1157d8098
21bd34812ce33fcc7dac5ec83961428969955b72b7de09ee33f9178a5afdc6be
```

Decision: CONTINUE to the actual signed relative cost/reserve, not another
mean or completion wrapper. This source removes centering terms, but a
filtered proof must still control its SAME surviving filtered variance.
The stronger optional initial-energy condition is not imposed as necessary.
An independently reviewed algebraic lead, NOT a new checked declaration:
after the center pin, r*s=jump(q^2)*jump(f^2). The existing
`lean/YMGap/Continuum/SU2QuaternionProductHeatJumpMean.lean:72`, `jump_mean`,
then yields X=2*(H[q^2*f^2]-H[q^2*P(f^2)]). This preserves the signed
quadratic response and supplies no sign or useful relative estimate.
The existing full angular/Ward/Taylor costs cannot be erased by oddness.

The latest user's lattice-measurement attachment matches the cached
`RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` review exactly. Retain its
channel-versus-every-state and physical-time calibration distinctions;
do not refetch papers or import fitted masses as constructive premises.

## Bounded loop-moment compression screen (2026-10-08 UTC)

Targeted primary-source research alongside the finite spatial-symmetry check;
not a routine arXiv listing scan and not a new proved scaling estimate.
Kazakov--Zheng's finite-N bootstrap uses SU(2) trace identities to close
Wilson-action loop equations on single traces. Its sections 3 and 4.2 use
Hermitian/reflection positive moment matrices and a Schwinger--Dyson-generated
finite hierarchy. Section 4.3 reports plaquette bounds and qualitative string
tension estimates; section 5 retains the local-region/large-loop bottleneck
and does not supply our scaling survival theorem. The action in equation (20)
is the exponential Wilson action, not the current finite heat-prefix action.
Do not import its loop equations unchanged.
[Primary paper, equations (1), (20), (76), sections 4.3 and 5](https://arxiv.org/html/2404.16925v2).

Root inspection and a bounded Sol read-only review locate existing original
constraints. `lean/YMGap/Continuum/BF4ExactSlabLocalHaarWard.lean:51`,
`fullAction_pair_pin`, retains every incident AND complementary heat factor;
`fullAction_local_ward:85` gives H[R*((DA)*f+A*(Df))]=0 with proved DR=0.
`fullAction_score_identity:106` is already present. There is no reason to
build that Ward interface again. From the literal `PolyQuaternion.conj:130`
and `PolyQuaternion.mul:138` in
`lean/YMGap/Continuum/BF4GeometricSpinNetworkMehler.lean`, scalar-component
algebra gives 2*sc(U)*sc(V)=sc(UV)+sc(U*conj(V)). This is a DERIVATION, not
a newly checked named trace-reduction declaration. Interpreting both terms
as actual source loops also requires compatible basepoints; conjugate is
inverse only with the unit relation. Full-action dependence cannot be
discarded under an independent-tail fusion hypothesis.

Critical normalization test: write S=ell(b*b), J=ell(b*T(b)). The existing
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131`,
`clearedRayleighCost`, gives C=Z1*S-Z0*J. The actual definitions
`lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:84`,
`originalOwnBlockVariance`, and `originalOwnBlockCost:89` give v=S/Z0,
e=C/(Z0*Z1). Algebraically, Z0*Z1*(c*v-e)=(c-1)*Z1*S+Z0*J.
Thus the normalized comparison is not an affine objective in unspecified
moments of ONE marginal: both chronological masses and OWN center must be
certified. Each lag retains its own Z0,Z1. A single stationary Wilson-action
moment matrix does not identify them or the current full heat transfer.

Decision: retain loop/SOS compression as an unimplemented candidate for an
exact finite certificate, only after its actual source basis, SAME-law Ward/
positivity constraints, normalization and omitted-mode error are supplied.
Rust may propose rational data; Lean must independently check it. Do not
launch an SDP, add a conditional certificate framework, or impose separate
per-lag positivity as a necessary condition for the signed aggregate.
The consumer is still `WindowSignedCost.aggregate_window_macro_ratio:181`
in `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean`; its complete
joint relative budget remains OPEN. No new mathematical proof or chart
closure results from this research screen.

## Full-cost and filtered-reserve screen (2026-10-08 UTC)

Root source inspection and two independent bounded read-only reviews; these
are mathematical DERIVATIONS, NOT newly kernel-checked declarations. No
compiler run, Lean edit, literature fetch or canonical proof-node closure.
The repeated lattice-measurement attachment is already covered by the
corrections in `RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`.

**Shared-link branch.** The proposed certified-W inequality
H[W Gamma_shared(a*f+b*g)] <= 8*a^2 H[W(2-d)]+8*(a-b)^2 H[W] is valid,
but it supplies no new cancellation or smallness. For the actual neighboring
faces at width>=2, the existing FULL arbitrary-signed identity at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentFullAngular.lean:425`,
`adjacent_full_angular`, with `cross_local:266` and `shared_squares:357`, gives

    Gamma_full(a*f+b*g)
      = 3*a^2*(4-f^2)+3*b^2*(4-g^2)+Gamma_shared(a*f+b*g).

Thus shared-link cancellation leaves THREE nonshared contributions per face.
Under the SAME certified W they are nonnegative, not uniformly strictly
positive: zero W/coefficients and small weighted deficits remain allowed.
`adjacent_full_angular_paid:451` already retains the equal-weight difference
square. The whole-family version already reaches the COMPLETE original
channel energy, with BOTH Taylor debts, at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:263`,
`family_coherent_energy_retained_square` (full angular identity at :163,
`family_coherent_full_angular`). PRUNE implementing the redundant shared-block
8/8 estimate. This does not rule out a useful whole-profile interacting bound.

**Filtering branch.** The consumer remains
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`, with finite square specialization
`original_window_budget_macro_ratio:245`. For a scalar eigenmode T*x=rho*x,
0<rho<1, x nonzero, R(n)=||x||^2*rho^n gives

    2*sum_{j<u}(R(2*u+2*j)-R(2*u+2*j+1))/R(2*u)
      = 2*(1-rho^(2*u))/(1+rho).

This exceeds one when rho^(2*u)<(1-rho)/2. A finite polynomial or Cesaro
filter either kills this eigenvector or only multiplies it; its surviving
relative cost does not improve. This screens a generic inference, NOT an
exhibited YM eigenvector or an actual YM-source counterexample.
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:122`,
`timeDefect_bound`, pays absolute decay against the PREIMAGE norm.
`lean/YMGap/Continuum/BF4WilsonAllNomeMacroRatioFilteredCost.lean:100`,
`retained_time_budget`, retains the earlier response; `macro_to_filtered_budget:123`
requires the missing macro survival ratio. Conversely,
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:102`,
`response_step_lower`, and `response_geometric_lower:117` propagate a supplied
selected-source Rayleigh floor, but do not produce a sufficiently slow rate.
NEXT is that ORIGINAL interacting source-specific reserve, or quantitative
slow-mode overlap, not another absolute-smoothing/completion wrapper. Keep
complete signed cost and SAME filtered OWN variance; a DIRECT filtered proof
remains eligible without a stronger unfiltered initial floor.

**Optional unfiltered profile route.** Bare full heat acts by w^12 on every
signed profile (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`,
`spatialSpan_fullRange`), independent of coefficient smoothness. This is NOT
an interacting-transfer eigenvalue. The original interacting identity is
E=12*(1-w)*V+R at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`,
`padded_family_energy_variance`; R is the COMPLETE signed `varianceRemainder:42`.
Put s=side(j), delta=afGap(j)=1-afNomeSchedule.nome(j), V>=0. If s*E<=c*V
and c<=6*s*delta, rearrangement gives R<=-6*delta*V, without inverting V.
The second condition holds after the computed
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:84`,
`afPowerBudgetCutoff`, with p=1, cap=c/6, by `afPowerBudget_gt:100`.
The schedule pin is
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:274`, `afNomeSchedule`.
This locates the needed negative leading-order response, but produces no bound
on R, energy lower bound or physical calibration. Do NOT apply Casimir 12 to
filtered b/A or make this optional stronger criterion necessary for that route.

Decision: retain the complete signed interacting estimate as the producer;
neither local coefficient smoothing nor generic time filtering replaces it.
No useful scaling budget or continuum survival is proved by this screen.
Whole Clay target remains OPEN; no chart reprint.

## Selected SAME-source filtered-profile join (2026-10-08 UTC)

Proposition: for any ORIGINAL radius-zero Wilson expression e, let
f=sourcePolynomial(e), K=headCutoff(w)+stage, c_stage its actual odd mean,
A=g_(stage+t), b=T^t(g_stage*(f-c_stage)). Prove that ell(b^2)/Z0 converges
to the EXISTING centeredTimeMoment(2t,state(e),state(e)); prove that the
literal clearedRayleighCost(A,b)/(Z0*Z1) converges to that moment minus the
moment at 2t+1. Z0=ell(A^2) and Z1=ell(A*T(A)) remain distinct. No inverse
norm, new action, completion or analytic smallness premise is needed.

Consumer: the actual filtered signed-profile cost in the generic completed
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`,
`aggregate_window_macro_ratio`. The published finite original window
specialization is still square-specific at `original_window_budget_macro_ratio:245`.
This selected increment constructs the finite numerator/denominator join,
not another conditional macro-ratio theorem or the analytic window budget.

Available inputs: arbitrary supported finite pins
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:140`,
`normalized_block_window_pin`, and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighWindow.lean:89`,
`clearedRayleighCost_window_pin`; the already generic completed pairing
`lean/YMGap/Continuum/BF4WilsonAllNomeZeroRadiusIncrement.lean:168`,
`time_pairing_lag`. Independent duplicate screening found that moving OWN
center convergence is still loop-specific. The old loop API must be retained;
extend it minimally and expose the computed mean threshold as data.

Reason for selecting this join: the actual family's Casimir-12 identity
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`,
`padded_family_energy_variance`, concerns the unfiltered spatialSpan.
It cannot simply be applied to the later filtered ratio b/A. Direct filtered
analysis must use the actual block cost/variance, not substitute a different
endpoint variance. Stop if a generic moving-center diagonal limit already
exists, a new analytic premise is needed, or old public statements change.

Predicted outcome: the fixed-member join is constructible from existing
original mixing/mean control. Mean cutoffs must be named computed data;
all limits fix w, width, e and t. Empty/constant/zero sources remain allowed;
no positive norm or changing-family conclusion is inferred. Budget: bounded
Sol implementation in two files, independent complete-source review, root
sole focused monitored checks with fresh memory/swap preflight, one worker,
20-GiB ceiling and 12-GiB reserve. No full-tree build/audit or chart closure.
Results are recorded separately below after verification.

### Observed source join and next mathematical decision

The selected fixed-member join is now kernel-checked:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.lean:104`,
  `expressionRaw_original_pin`, transports the complete source polynomial
  through its actual padded chronological window. At :128,
  `expressionCenteredTimeMoment_chronological_pin` identifies the EXISTING
  completed centered moment, not a replacement functional.
- The named computed cutoff at :158, `expressionEndpointMeanThreshold`,
  combines the original singleton joint modulus with a geometric cutoff.
  `expressionEndpointMean_approx:164` gives both approximation inequalities;
  `expressionOwnMean_converges:225` retains the actual odd-window mean.
  `expressionOwn_centeredPair_converges:251` expands this moving center
  before taking the fixed-expression limit.
- `lean/YMGap/Continuum/BF4WilsonAllNomeOriginalRayleighLimit.lean:84`,
  `originalOwnBlockVariance`, and :89, `originalOwnBlockCost`, construct
  exactly the quantities selected above. Their finite pins are
  `originalOwnBlockVariance_pin:96` and `originalOwnBlockCost_pin:104`.
  `originalOwnBlockVariance_converges:130` and
  `originalOwnBlockCost_converges:143` give precisely the SAME lag-2t
  centered moment and its lag-(2t+1) difference. Only positive chronological
  vacuum partitions are inverted; no observable norm is inverted.
- The three old single-loop APIs at OwnCenterLimit :305/:314/:323 remain
  specializations. The unchanged
  `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean`
  also passes a focused consumer regression against the generalized API.

Independent complete-source review passes, including the final technical
repairs. Root alone ran the serialized checks, each with one worker,
a hard 20-GiB ceiling, 12-GiB reserve and fresh process/memory/swap preflight:

| Final focused check | Log | Printed axiom gates |
| --- | --- | --- |
| WilsonOwnCenterLimit | `/private/tmp/ym-expression-own-center-20261008d.log` | 12, all exactly `{propext, Quot.sound}` |
| OriginalRayleighLimit | `/private/tmp/ym-expression-original-rayleigh-20261008b.log` | 6, all exactly `{propext, Quot.sound}` |
| unchanged square consumer | `/private/tmp/ym-expression-square-regression-20261008a.log` | 4, all exactly `{propext, Quot.sound}` |

Initial checks caught omitted proof-only section binders, doc/include order,
opaque raw-pair elaboration and an implicit convergence sequence. Those
were repaired without mathematical statement changes. Failed-check
`sorryAx` output is NOT proof evidence; every final gate is clean.
Source SHA-256 values, in the same order as the table:

```
79d5aeb211903d306396430a2f0c16a81d2b58e2ebc9abb9622d6c0d763d79f7
ec1ad9e7fd2dd28bf2cce0655686b2fd8497a922a99b401bf224614ac9229c5c
cc4e387b51929dfd2e29cdc408cd1fcb8d70fae38bf1b8444973090ca9cb0957
```

Decision: continue the JOINT signed-profile cost estimate against this
SAME filtered variance. No more source/limit wrapper is needed for a fixed
radius-zero member. The existing literal split at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:244`,
`original_block_rayleigh_split`, retains energy, terminal drift and signed
multiplication cost together. Its :283, `terminal_clearedRayleighCost_le`,
pays the boundary term but leaves the energy and signed commutator unpaid.
The initial-source `FamilyMarginPencil.pencil_contract:278` is not a
filtered-cost estimate. None of these facts justifies substituting the bare
family Casimir identity for the later ratio b/A.

No new analytic premise, hole, axiom, proof limit, canonical field or broad
chart status changed. Nome, spatial width, expression and lag remain FIXED;
changing-family/spacing control, macro survival, nontrivial continuum,
physical mass, QFT axioms and every-group Clay closure remain OPEN.
The root import is registered only; no root/tree build or audit was run.
The user's lattice-measurement note remains incorporated with the primary
source corrections in `audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`;
no measured mass, finite-spacing Hamiltonian identification or area-law
inference is imported as an analytic premise.

### Parallel source screening retained in this decision

No adaptive-order interacting remainder producer was found in the inspected
source. The strongest relevant produced source error is cubic Sobolev plus
the omitted heat tail:
`lean/YMGap/Continuum/SU2QuaternionCyclicSobolevProjection.lean:89`,
`sourceError_le_sobolev`. It retains actual derivatives of q, q*f and q*f^2,
q=projectedEndpointSource(V*g_depth), not just bare family degree 12.
`completeRemainder_le_sobolev_completedSquare:138` already retains the
negative commutator square; do not rebuild that cancellation.

Global sum(c_p)=0 does not remove the quadratic Ward matrix. From
`lean/YMGap/Continuum/SU2QuaternionWeightedCasimirWard.lean:45`,
`blockResidual`, the residual of F=sum c_p*f_p is a sum of
c_p*c_q*H[(f_p-mu_p)*(JW)*(Jf_q)]. Even granting equal means, coefficients
(1,-1) leave W_pp+W_qq-W_pq-W_qp. The existing coherent row sum only uses
incident faces (`FamilyCoherentTail.aggregateCoherentTail:92`); disjoint
opposite coefficients do not cancel singleton link rows. No new zero-sum
or summation-by-parts smallness premise is adopted.

No produced blocking estimate fills the AF original filtered budget:
`lean/YMGap/Continuum/CompactDualCutoffOnePhysicalPushforward.lean:290`,
`physicalRemainderL1_le_two`, is only a cutoff-one cap of TWO;
`lean/YMGap/Continuum/Z4DyadicSpinFourFineCouplingNormalizedBalancedBridge.lean:371`,
`centeredCylinderRemainder_abs_le_of_balanced_and_margin`, explicitly takes
the missing balanced and margin estimates. The scale-five fusion prefix
does not produce the original action/fusion-power pins. These are dated
source checks, not fresh compilation or a nonperturbative error bound.

## Selected fixed-power AF payment test (2026-10-08 UTC)

The spatial-profile screen has a real microscopic degree advantage: the
existing `FamilyHeatEigen.spatialSpan_fullRange` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`
has factor w^12 independent of family size, unlike the growing square.
However `AFPaddedTrajectory.afBareHeatLoss_no_uniform_cap` at
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:451` already
rules out deriving uniform rescaled H1 from that factor alone. The actual
`FamilyVarianceTaylor.padded_family_energy_variance` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`
retains 12*(1-w)*OWN variance PLUS the unpaid signed remainder.

Next mathematical test: on the ACTUAL afGap(j), construct an all-tail
cutoff for C < side(j)*afGap(j)^p, for EVERY fixed natural p and rational C.
The linear denominator bound gives 3*(j+1)*afGap(j)>=1; the existing
`PolynomialGeometricDecay.polynomial_bound` at
`lean/YMGap/Continuum/PolynomialGeometricDecay.lean:99` supplies the
constructive exponential/polynomial comparison and explicit cutoff.
This tests whether a selected POSITIVE scalar payment with a nonzero fixed
coupling-power term can itself meet an O(1/side) budget, including a
quadratic Taylor prefactor. It supplies no lower bound on an actual energy,
moment or remainder; exact cancellation and sharper estimates remain
possible. It is not a physical-spacing calibration or an obstruction to YM.

Prediction: that scalar budget fails even at arbitrarily high FIXED power;
degree zero must be included. Stop if the statement already exists, the
original schedule is replaced, or the proof needs a new asymptotic premise.
One bounded Sol leaf, independent mathematical review, root sole focused
monitored check, one 20-GiB worker and 12-GiB reserve with fresh dynamic
preflight. No broad build/audit, limit increase, frontier-field change or
generic conclusion-as-input. Observations will be recorded separately.

### Observed result and decision

The selected statement is now kernel-checked on the unchanged schedule:

- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:41`,
  `afGap_linear_floor`: 3*(j+1)*afGap(j)>=1, including index zero.
- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:84`,
  `afPowerBudgetCutoff`: computed ALL-TAIL cutoff, no existential extraction.
- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:100`,
  `afPowerBudget_gt`: C<side(j)*afGap(j)^p at EVERY index past that cutoff,
  for every FIXED natural p and arbitrary rational C.
- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:156`,
  `afPowerBudget_no_uniform_cap`: no eventual cap for a fixed p.
- `lean/YMGap/Continuum/BF4WilsonAllNomeAFPowerBudget.lean:167`,
  `afPowerBudget_adaptive_le_one`: side(j)*afGap(j)^j<=1 for every j.
  This supplies no control of degree-dependent Taylor constants.

Interpretation: PRUNE fixed-order positive scalar payments alone. Replacing
power two by any other fixed power cannot by itself provide an inverse-block
budget on this schedule. Retain signed cancellations and genuinely adaptive
estimates; neither is refuted or produced by this leaf. In particular
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceTaylor.lean:151`,
`energy_le_angular_add_quadratic`, retains (1-w)^2*sourceTaylorBudget:
there is no supplied uniform nonzero coefficient or lower bound turning
that actual source-dependent budget into the selected scalar payment.
`JointQuadraticDebt` uses 1-w^(4*side), not literally 1-w; do not equate it
with this quadratic-prefactor screen.

NEXT: the actual JOINT signed cost versus SAME surviving filtered variance,
using the existing window consumer. Any adaptive-order proposal must FIRST
produce the actual interacting remainder with its order/source/volume
constants; no new generic asymptotic wrapper is selected. Main scaling,
continuum survival, physical calibration, OS/QFT, all groups and Clay OPEN.

Verification: Sol's bounded leaf, independent full-source mathematical PASS,
root full-source review, one final focused monitored check on 2026-10-08 UTC.
Preflight found no competing compiler/runner, 87% reported available memory
and zero swap; one worker, hard 20 GiB ceiling, 12 GiB OS reserve. The first
check exposed only missing explicit unfolding of rational one's numerator
and denominator in a private helper; root repaired it without statement or
limit changes. Its failed axiom output is NOT evidence. Final log:
`/private/tmp/ym-af-power-budget-20261008b.log`; cutoff is axiom-free and
all four public theorem gates are exactly {propext, Quot.sound}. Source
SHA256: `857130af1272820cfc6165b713c67cca6a065b63b4af981f2bff597a424564da`.
Root import registered, not rebuilt. No full-root/tree build/audit/guard,
baseline refresh, new sorry/axiom/classical/native shortcut, canonical field
change or broad chart closure/reprint.

## Weighted chronological sign screen (2026-10-08 UTC)

### Follow-on square-completion screen (source review only)

Independent mathematical review and root source inspection, 2026-10-08 UTC.
This is a PAPER reduction, not a new Lean theorem or a produced scaling bound.
Retain T=K*M_V, ell_V=H[V*], a=g_d, A=Ta, z=ell_V[a^2], v=ell_V[A^2],
the supported incoming phi and a spatial insertion Theta. On the original
two-endpoint kernel define

```text
P(x,y) = K(x,y)*V(x)*V(y)*a(x)*A(y)
C      = ell_V[a*phi^2*(T(Theta*A)-Theta*T(A))]
M      = H2[P*phi(x)^2] = ell_V[a*phi^2*T(A)]
JTheta = H2[P*phi(x)^2*(Theta(y)-Theta(x))^2].
```

The original kernel/action/terminal positivity certificates make P positive.
For each positive rational tau, expanding the two literal nonnegative
squares P*(phi(x)*(Theta(y)-Theta(x)) +/- tau*phi(x))^2 gives

```text
  +/- 2*tau*C <= JTheta + tau^2*M.
```

Thus square completion needs no fourth power of phi or source inverse, but
the full chronological residue still contains BOTH the commutator z*C and
ell_V[a*phi^2*Theta*(z*T(A)-v*a)]. This is not a sign or stationary-law pin.
The exact existing SAME endpoint identity is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lean:86`,
`lastStepNoise_endpoint_pin`: M contains innovation PLUS the outgoing source
norm. It is not the surviving variance alone. The actual positive Ward
payment retains the additional spatial insertion T(Vbar*A), by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`,
`original_ratioNoise_gradientPayment_weighted_pin`.

No supporting producer bounds the source-weighted action-jump square JTheta
and chronological defect jointly by the required SAME surviving variance.
In particular
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceTaylor.lean:132`,
`energy_taylor_angular`, has the actual projected source and BOTH outgoing
signed remainders; it does not assert a matching negative JTheta. Do not
substitute its density for P or cancel unlike weights. Decision: retain this
screen as an explicit unpaid moment, not another conditional square-bound
module. The coupled signed window estimate remains OPEN.

Duplicate screen resolved: the suggested converse from represented dyadic
quotient convergence to coordinate range/graph witnesses is ALREADY in
`lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeInputRange.lean:69`,
`inputRange`, and `representedGraphOfQuotientLimit:94`. Do not rebuild it.
No Lean edit, compiler, new hypothesis, canonical field or chart delta from
these source reviews.

Selected proposition: test whether original-form positive weighted transfer,
chronological partitions and OWN centering alone sign the additional weighted
time residue. Its source consumer is the proposed adjacent-stage cancellation
of the positive incoming Ward payment, not a new physical frontier bundle.

Source-level algebra (NOT a new Lean theorem) from
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:97`,
`transferStep_weighted_symmetric`, generalizes
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNoiseDissipation.lean:86`,
`lastStepNoise_endpoint_pin`. With A=Ta, b=T(a*phi), N=A*T(a*phi^2)-b^2,
z=ell_V(a^2), v=ell_V(A^2), the cleared weighted difference equals

```text
z*(ell_V[Theta_out*N]+ell_V[Theta_out*b^2])
  -v*ell_V[Theta_in*(a*phi)^2]
 = ell_V[a*phi^2*(z*T(Theta_out*A)-v*Theta_in*a)].
```

Setting BOTH Theta weights to Vbar retains
`z*(T(Vbar*A)-Vbar*T(A))+Vbar*(z*T(A)-v*a)`.
Neither the spatial transfer commutator nor the chronological vacuum defect
is removed by partition multiplication. The incoming Ward density genuinely
contains T(Vbar*A): `RatioNoiseWardAbsorption.original_ratioNoise_gradientPayment_weighted_pin`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`.
The complete derivative also retains J(V):
`LastStepSourceDerivative.lastStepSourceDerivative_expansion` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:80`.

NEW CHECKED diagnostic in
`lean/YMGap/Continuum/RationalWeightedTemporalResidueObstruction.lean`:

- `heat_kernel_pin:60`, `transfer_symmetric:75` and `transfer_positive:112`
  certify the actual two-state K=[[3/4,1/4],[1/4,3/4]], V=(2,3), T=K*M_V.
  Weighted symmetry and positivity hold for ALL rational probes, not just
  the counterexample. K has positive entries and unit row mass.
- `chronological_pins:126` computes A=(9/4,11/4), z=5/2 and v=525/32
  from the literal a=1. `own_mean_pin:144` centers f=(1,0) in the actual
  VaA edge law: mass=51/8, mean=6/17. `own_variance_positive:149`
  rules out a degenerate excitation. `noise_pin:163` gives N=(9/8,9/8).
- `centered_residue_pin:154` gives the positive integral 3045/9248.
  `weighted_time_difference_pin:173` retains the extra spatial insertion,
  BOTH computed partitions and complete noise; `weighted_time_difference_positive:174`
  proves that exact difference is positive. No inverse approximation or
  stationary source is substituted.

Decision: PRUNE ONLY automatic nonpositive weighted-telescope residue from
those generic inputs. This d=0 two-state diagnostic is not an SU(2) action,
a positive-filter-depth BF4 counterexample or a refutation of the full two
signed Ward responses plus BOTH Taylor terms. It pays no actual scaling cost.
NEXT remains a source/action-specific JOINT estimate against the SAME surviving
variance, consumed by `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`. The parallel projected-q^2 Ward screen
also supplied no favorable sign or useful joint inequality; no raw-q^2
standalone cap is promoted to a necessary hypothesis.

Root complete-source and independent complete-source mathematical reviews PASS.
One focused monitored check passes; all 17 printed gates are permitted (13
axiom-free, four exactly {propext, Quot.sound}). Final log:

```text
/private/tmp/ym-weighted-temporal-residue-20261008a.log
SHA256 4de38b69e80606ee038d574dd6f547c611a4a3d24044a9b95869f7bd00c64396
```

Fresh preflight: no competing compiler, 87% system-wide free and zero swap.
One worker, hard 20-GiB ceiling and 12-GiB reserve. Root import registered only;
no root/full-tree build, audit, guard, baseline refresh, hole, axiom or canonical
field change. Broad chart claims unchanged; no reprint.

## Live source reconciliation and checked SAME-OWN contraction (2026-10-08 UTC)

Historical NEXT entries in this audit do not override the current source.
Current-source independent reviews find the scalar addition-square, radial
ceiling and their original-prefix Haar/frozen joins already constructed:
`lean/YMGap/Continuum/ThetaCompletedAdditionSquare.lean:179`,
`cleared_addition_square`;
`lean/YMGap/Continuum/ThetaProductRadialCeiling.lean:112`,
`productRadialCost_le_cap_add_tail`;
`lean/YMGap/Continuum/JacobiHeatRadialHaarCertificate.lean:182`,
`radialCertificate`; and
`lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixCurvature.lean:88`,
`prefix_frozen_curvature_adaptive_certificate`.
Those are existing producers, not new checks in this checkpoint. Do not build
another tail/addition/strict-floor wrapper. The actual missing quantitative
input remains joint original action/source response control, including the
retained density/spatial derivatives, reconstruction/drift and BOTH Taylor
remainders against the SAME surviving filtered variance. The concrete consumer
is `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`.

Selected mathematical increment: contract the existing connected-Gram raw
mixed moment, rather than require a standalone raw-to-OWN ceiling. Available
inputs: the literal symmetric sum test, SAME product heat pairing/symmetry,
original projected-source energy and OWN centered-square pins. Pointwise,

```text
(q+q')^2*(psi+psi')^2
  = (q-q')^2*(psi+psi')^2 + 4*q*q'*(psi+psi')^2.
```

The second integral equals 8*S+8*B=16*S-8*E. No source positivity,
stationary eigenpin, normalized-law substitution, source/variance inverse or
new analytic premise is needed. Test arbitrary supported sources, zero
denominators/depth zero, actual observable fringe guards and BOTH mean
corrections. Verification budget: two serialized narrow 20-GiB checks, root
sole compiler, independent complete-source review. Stop on a source/energy
substitution or a claimed positive credit from Gram positivity alone.

Observed VERIFIED PROGRESS:

- `lean/YMGap/Continuum/SU2QuaternionProductHeatSumNorm.lean:229`,
  `sourceSumIncrementCost`, defines literal Dplus=H[K*(jump q)^2*(sum psi)^2].
  `sourceSumIncrementCost_nonnegative:235` produces Dplus>=0 from the actual
  product-heat certificate; `sumTest_norm_energy_pin:256` proves the exact
  16*S-8*E+Dplus norm. The heat list and every supported factor remain.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:292`,
  `centered_sourceSumIncrement_nonnegative`, instantiates that residue on the
  actual projected endpoint and OWN center. `centered_norm_energy_pin:308`
  supplies S=oddMass*OWN oddVariance and the ORIGINAL energy. Explicit
  observable fringe independence is retained; no raw-q^2 mean is substituted.
  `centered_denominator_energy_pin:350` keeps the actual -M^2, giving
  V=16*S-8*E+Dplus-M^2. `original_centered_energy_response_budget:370`
  consumes it in the existing 4*V*E+V*J^2+X^2<=2*V*C inequality, with
  unchanged J, M and X=Cov(r,s). Degenerate V remains covered; no division.

Decision: CONTINUE joint response control. Dplus>=0 is not an upper estimate
for V, so this identity alone pays no useful fraction. It removes the need to
express the residue as an independently bounded raw mixed moment; it does
not make that moment comparison automatic. A joint credit may retain
X^2-(Dplus-M^2)*Var(r); no lower bound on it is proved here. No initial-energy,
filtered-survival, scaling or completed physical/Clay node is closed. The
separate cofinal AF necessity shows why a useful initial fraction on the
unfiltered square schedule needs large original cancellation; see the
interacting-response-shape audit. Keep unfiltered and filtered norms distinct.

Root inspected the complete final sources; independent complete-source
mathematical review PASS. Both final focused checks pass, all seven new
printed declarations stay within {propext, Quot.sound}. Unlike the AF probe,
the sourceSumIncrementCost definition has permitted dependencies; it is not
reported axiom-free. Logs:

```text
/private/tmp/ym-source-sum-energy-pin-20261008a.log
SHA256 be05611ef4fdd5ca36288750118b7497e06a5ddcf43db2d7639787acc60481a7

/private/tmp/ym-own-source-response-denominator-20261008a.log
SHA256 53481cb7f24b793e70e92ea22bc20cd2c852bb4ffb69af904478b39bf6abed94
```

Fresh preflights found no competing compiler/runner, 88% system-wide free
and zero swap. One worker, hard 20-GiB ceiling and 12-GiB reserve; no limit
increase. No new imports in the two leaves, no full-root/tree build/audit,
baseline refresh, sorry/axiom, canonical field change or chart reprint.

## Selected reciprocal-free positive gradient payment (2026-10-08 UTC)

### Selected exact incoming-density trace (2026-10-08 UTC)

Next bounded identity: `H[Vbar^2*A*T(a*(Jphi)^2)]`
`=ell_V[a*(Jphi)^2*T(Vbar*A)]`, with a=g_d and A=Ta. Produce fringe
independence of the transferred gradient square, apply actual fringe Fubini
and ORIGINAL weighted transfer symmetry. No sign or nome/cutoff positivity
is needed. Consumer: the checked unit-gradient Ward payment can be expressed
in original incoming coordinates without identifying it with another density.
Prediction: BOTH the active Vbar factor and the additional temporal step
remain. Actual marginalAngular uses a*Ta, not a*T(Vbar*Ta). Thus a direct
coefficient-one marginal-energy/variance join is unavailable. Stop if the
pin drops Vbar, identifies T(Vbar*A) with A/TA, or silently uses raw-family
gradient control for the filtered reconstructed ratio. One existing changed
leaf, independent review, root-only monitored 20-GiB check; no new interface.

Observed: VERIFIED exact incoming-density identity. In
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:384`,
`original_ratioNoise_gradientPayment_weighted_pin` proves the displayed pin
for arbitrary rational nome/cutoff and supported phi. Phi need NOT be fringe
independent: independence of Ephi is produced by the actual transfer image.
Both the original spatial weight V and the literal T(Vbar*A) survive.
Final focused check `/private/tmp/ym-ratio-noise-incoming-density-20261008a.log`
passes all six printed gates exactly {propext, Quot.sound}; source SHA256
`272d9b089299597e99bf2f9b87b6c4f46b574be346c3d9b0ddb07020f0428512`.
Independent full-block review PASS. Preflight: 87% system-wide free, zero swap,
no competing compiler; one 20-GiB worker/12-GiB reserve. No full-tree audit,
new hypothesis bundle, hole, axiom or canonical field/diagram closure.

Decision: PRUNE the direct coefficient-one identification with marginalAngular
or normalizedEnergy. This is not a refutation of a possible joint signed
bound. The actual incoming marginal angular density is V*a*Ta:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAngularMarginal.lean:51`,
`marginalAngular`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:130`,
`marginal_middleRatio`, pins its original chronological law. Even an ordinary
spatial cap first gives T(Vbar*A)<=C*T(A)=C*T^2a, so a further terminal
comparison is needed; neither factor is coefficient one or a useful scaling
estimate. Do NOT implement that coarse ceiling as another claimed producer.

Existing Taylor rebasing does not supply the missing cancellation (SOURCE
REVIEW, not an impossibility theorem). `AngularMarginal.angular_weight_identity:104`
converts q_d^2*Gamma(f) to q_d*P(q_d)*Gamma(f) for the SAME source and f.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMarginalTaylor.lean:64`,
`signedRemainder`, retains that defect; `energy_taylor_marginal:71` performs
that rebasing, not a removal of Vbar inside a subsequent transfer.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSignedScorePayment.lean:235`,
`exactScoreAngularBudget_terminal_signed_payment_le`, uses incoming phi at n,r;
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:218`,
`exactScoreSignedBulk`, retains outgoing phi at n,r+1 and its own numerator,
reciprocal degree and BOTH Taylor terms. Those observables are not equal.
CONTINUE only with action/source-specific JOINT control across these literal
transitions, or an independent actual signed response credit. No supplied
conclusion, raw Wilson Casimir substitution or changing-family survival claim.

Independent frozen-source operator-view screen (2026-10-08 UTC, source review
only): `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:267`,
`energy_identity`, already pins twice the original energy to the division-free
edge jump form. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepPredictionEnergy.lean:201`,
`lastStepPredictionResidual_energy_pin`, retains the original diagonal V*a*Ta.
Neither statement compares that measure with the next V*Ta*T^2a or bounds
the unpaid coupled Ward/Taylor expression in the next surviving norm.
Do not re-export these identities as a new scaling producer. The alternate
initial-energy consumer already exists at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalEnergyTransport.lean:224`,
`original_block_cost_le_initial_energy`; its literal `hlocal` input remains
to be produced with a useful changing-family fraction. No new Doob wrapper,
conditional frontier field or proof claim is added by this screen.

Independent SU(2)-harmonic response screen (2026-10-08 UTC, source review
only): `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonWord.lean:248`,
`productMap_fundamental_word`, pins the bare ordered fundamental word, not
the interacting product q*F. The literal source in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:60`,
`squareHeatMultiplicationDefect`, retains q=V*terminalMessage;
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean:70`,
`spatialWeight`, and `BF4ExactSlabFixedSpatialTransferStep.lean:51`,
`transferStep`, reinsert the full spatial action before heat smoothing.
No bounded-spin hypothesis for q or reconstructed filtered ratios is produced.
The exact unpaid response is retained by
`BF4DyadicWilsonSquareSignedHeatDefect.lean:129`,
`paddedSquare_energy_signedHeatDefect_identity`:
E=(1-w^(12*side))*S-signedGain, with S=oddMass*OWN oddVariance.
The existing all-index AF loss budget
`BF4WilsonAllNomeAFPaddedTrajectory.lean:461`,
`af_squareLinearHeatBudget_ge_one`, and
`BF4DyadicWilsonSquareBareTransmissionNecessary.lean:74`,
`bare_transmission_floor_necessary`, imply on paper that this bare
transmission is at most 1/2. Thus a useful E<=c*S requires a positive
interaction gain at least (1/2-c)*S, not just a small absolute remainder.
This consequence is a source-level mathematical screen, NOT a newly checked
Lean theorem, energy lower bound or obstruction to Yang--Mills itself.
`BF4DyadicWilsonSquareWardMoments.lean:385`, `paddedSquare_ward`, computes
the literal Ward moments but supplies neither their useful joint sign nor
their complete remainder estimate. Do not import the bare eigenpin into the
different incoming weight V*a*T(Vbar*Ta). CONTINUE action-specific JOINT
response/Taylor control; no new harmonic-response wrapper is justified.

Independent localized-pair screen (2026-10-08 UTC, source review only):
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:208`,
`original_centered_energy_budget`, retains actual
q=projectedEndpointSource w K width (terminalMessage w K width depth), psi=F-OWNmean,
r=(q-q')*(F-F') and s=(q+q')*(psi+psi'). Their product can be expanded on
paper as (q^2-q'^2)*(psi^2-psi'^2); bare character transmission then concerns
raw projected-source q^2 moments, NOT automatically the OWN qPq moments in
`BF4DyadicWilsonSquareWardMoments.lean:385`, `paddedSquare_ward`.
`BF4ExactSlabFixedSpatialSourceVarianceGram.lean:138`,
`centeredNormExpression`, and `centered_sum_norm:145` retain the complete
sourceIncrementCost, centeredMixedMoment and interacting variance. The
nonnegativity theorem `centered_denominator_nonnegative:175` is not their
useful upper comparison. No source-level raw-to-OWN moment or localized
mean-crossing payment was found in this inspected route. The existing
positive spectator-band response
`BF4DyadicWilsonSquareSpectatorResponse.lean:237`,
`paddedSquare_energy_band_cleared`, is not a new order-one gain producer.
These are source/math reviews, not newly checked Lean response identities,
integrated energy lower bounds or an obstruction to the BF4/Yang--Mills
estimate. Do not add a localized-certificate interface assuming the missing
statistical payment. The actual JOINT relative response estimate remains
the primary frontier.

Bounded estimate: on ACTUAL a=g_d, A=Ta, Ephi=T(a*(Jphi)^2), Vbar and
the existing finite G_k(A), test H[Vbar^2*G_k^2*A^3*Ephi]
<=H[Vbar^2*A*Ephi], coefficient ONE for every finite k. Produce the A
window, A/Ephi positivity and multiply the existing certificate
1-(A*G_k)^2 by Vbar^2*A*Ephi. No precision onset, floor penalty, new source
inverse, historical-noise widening or action replacement. Prediction: the
only positive gradient payment in the actual Ward consumer loses its
outgoing-degree dependence; both signed G_k-dependent responses remain.
This is not smallness relative to surviving variance. Root bounded extension
of the existing leaf, independent review, one narrow monitored 20-GiB check.
Stop if Ephi positivity is not produced or either signed response is dropped.

### Observed result / decision

VERIFIED PROGRESS: the existing Ward leaf now proves
`original_ratioNoise_gradientPayment_unit_le` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:253`.
Actual terminal/transfer certificates produce positivity of A and Ephi and
the actual output window, including d=0. The positive difference is certified
as `Vbar^2*A*Ephi*(1-(A*G_k)^2)`, for EVERY k including zero.
`original_ratioNoise_ward_unitGradient_le:323` consumes it at k+1 and retains
BOTH signed responses verbatim. No precision onset or numerical floor loss
remains in this positive payment. Discarding the finite multiplier is an
upper-envelope simplification, NOT a sharper numerical bound.

Final focused check: `/private/tmp/ym-ratio-noise-unit-gradient-20261008b.log`,
all five printed gates exactly {propext, Quot.sound}. Final source SHA256:
`f5ccbf8493173599d98038c793ef6f0af953ca7c2afcac1af247d489aea9c697`.
Independent complete-block review PASS. Fresh preflights: 87--88% system-wide
free, zero swap, no competing compiler; one 20-GiB worker/12-GiB reserve.
No full-tree check, new hole/axiom, field weakening or chart-claim change.

KEEP the new literal consumer. The bare positive payment is still an ORIGINAL
interacting incoming-gradient moment, not the SAME surviving variance. The
two signed density/spatial responses retain G_(k+1). Their useful joint
source-specific comparison, reconstruction/drift and BOTH signed Taylor
remainders remain the next producer for `original_window_budget_macro_ratio`.
Independent source review found no supplied initial O(1/u) energy fraction;
posterior mixture score variance is not removed by component log concavity,
and the raw Wilson Casimir does not bound the reconstructed filtered ratio.
These last route screens are source review, not new Lean estimates.

## Observed noise derivative and ONE-cross Ward absorption (2026-10-08 UTC)

Classification: VERIFIED PROGRESS for the following finite original-source
identity/estimates; SOURCE-LEVEL REVIEW ONLY for the joint-IBP screening below.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseDerivative.lean:171`,
`ratioNoise_derivative_carrier`, proves the pre-registered cleared identity
with complete g=V*a, actual K, A=Ta, b=T(a*phi), U=T(a*phi^2), N=AU-b^2
and X=lift(A)*phi-lift(b). It preserves EVERY surviving insertion.
`weightedNoise_derivative_carrier:243` retains arbitrary output V and J(V^2N).
It assumes no positivity, exact ratio/inverse or stationarity.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption.lean:195`,
`original_ratioNoise_phiGradient_absorption_le`, produces the ACTUAL terminal
law and its positive window. Its conditional square is
I[K*g*(lift(JA)*X+lift(A^2)*Jphi)^2]
=A*(N*(JA)^2+2*A*(JA)*Mphi+A^3*Ephi).
Positive-multiplier reflection gives
-H[R*(N*(JA)^2+2*A*(JA)*Mphi)]<=H[R*A^3*Ephi]
for arbitrary certified R. Coefficient ONE; no N/A inverse or lower-floor
factor in the bound. Reflection is integrated order, not division of a
certificate. `ratioNoiseGradientMoment:68` and `ratioNoiseGradientEnergy:74`
retain literal original incoming moments. Depth d=0 is permitted because
the produced output window is for g_(d+1).

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:115`,
`original_ratioNoise_ward_absorption_le`, uses the ACTUAL successor reciprocal
G_(k+1)(A), Vbar=spatialFringeMass, F=Vbar^2*N and R=Vbar^2*G^2. Noise,
output certificates and the upper window are PRODUCED. The one-plane result is
H[F*G^2*(A*J^2(A)-(JA)^2)]
<=H[R*A^3*Ephi]-H[R*(JA)*I[K*(Jg)*X^2]]
  -2*H[A*G^2*(JA)*Vbar*(JVbar)*N].
`ratioNoiseDensityMoment:57` retains FULL J(V*a), and
`noiseDerivativeIncoming_moment_pin:65` proves the exact density+2*A*Mphi
split. Input V and output Vbar remain distinct. Incoming phi is arbitrary
supported data; no incoming/outgoing reciprocal-degree identification.

Root and independent complete-source mathematical reviews PASS. Final
focused logs PASS, all 13 printed gates exactly {propext, Quot.sound}:
`/private/tmp/ym-ratio-noise-derivative-20261008b.log` (seven),
`/private/tmp/ym-ratio-noise-absorption-20261008c.log` (three),
`/private/tmp/ym-ratio-noise-ward-20261008a.log` (three).
Earlier checks exposed namespace, negation-support, proof-composition,
transport-orientation and reflexivity elaboration typos; their repairs change
no theorem statement or resource limit. Failed-check output is NOT evidence.
Fresh preflight before EVERY launch: 87--88% free, zero swap, no competing
Lean/Lake/pytest/runner. One 20-GiB worker/12-GiB reserve, root sole compiler.
Root imports registered only; no root/tree build, full audit/guard or baseline
refresh. No source sorry/new axiom/classical/native shortcut or field weakening.
Checked-source SHA256 (Derivative / GradientAbsorption / WardAbsorption):
`515795cba822f9e9e1d3df9ec571215089befa358bd0dc44f8bbeac2724a82d2`,
`dd788690bf2a8d51a32e8b2c4fddeadbc15f47a28dba49e4543407b667ddf92e`,
`bd9ebc8a0dcf9daa3e9bffee2894e4f37572f6c86d49798be76afdb3334b80d3`.

### Decision / next actual estimate

KEEP the coefficient-one payment and literal signed responses. REPOINT to
action/source-specific coercivity or cancellation controlling them jointly
with the incoming-gradient payment, reconstruction, drift and BOTH signed
Taylor remainders on the filtered OWN-centered padded Wilson family.
The actual aggregate input remains
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`: an eventual normalized original-window
cost bound against the SAME surviving variance. Its chronological partitions
remain distinct; no universal arbitrary-source noise cap is requested.

Independent source-level screening combines the two retained signed terms
on the actual edge as -H2[K*G_y^2*D_y*X^2*(J_x+J_y)(g_x*Vbar_y^2)].
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularForm.lean:64`,
`productHeat_pairedAngular_carrier`, removes the simultaneous K derivative,
not the action derivative. Joint Haar IBP then reintroduces the paid phi
cross and returns to the existing Ward identity. This is NOT a newly checked
bound or counterexample; PRUNE implementing that circular rearrangement.
Fringe independence permits conditional integration, not active-link action
derivative cancellation. OWN centering supplies a global moment constraint,
not a sign for this innovation-weighted density term. The separate gauge
review likewise found no symmetry-only linkwise orthogonality/cancellation.

No useful initial energy fraction, complete surviving-form scaling estimate,
continuum survival, completed OS, physical mass, SAME limiting QFT, every-group
or Clay claim closes. Canonical displayed claims are unchanged; no chart reprint.
The user's measurement guidance is already incorporated with primary-source
corrections in `RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`; numerical
channel masses provide no premise or replacement for these analytic inputs.

## Selected absorption of the incoming observable-gradient cross (2026-10-08 UTC)

Bounded estimate to test after the derivative pin: with the same actual
g=V*a, A=T(a), N, X, define M=I[K*g*X*J_in(phi)] and
E=I[K*g*(J_in(phi))^2]. The square
I[K*g*(lift(J(A))*X+lift(A^2)*J_in(phi))^2]
expands to A*(N*J(A)^2+2*A*J(A)*M+A^3*E).
For ACTUAL terminal a and its PRODUCED positive A window, reflect that
multiplier inside Haar order to obtain, for certified R,
-H[R*(N*J(A)^2+2*A*J(A)*M)]<=H[R*A^3*E].
Prediction: coefficient ONE, no inverse of N or A and no lower-floor loss
in the estimate. Existing partial-square positivity and quantitative
positive-multiplier reflection are the intended inputs.

Consumer: the favorable negative square exposed by the weighted derivative
pin absorbs precisely its incoming observable-gradient cross. The spatial
and COMPLETE incoming-density derivative terms remain signed and OPEN;
no initial energy fraction, surviving-form bound or scaling result follows.
One bounded implementation leaf with an actual terminal consumer that
PRODUCES its window/positivity, independent source review and root serialized
narrow 20-GiB verification. Stop or revise if the square loses a factor of A,
the reflected weight is not produced, or a noise/source inverse is introduced.

## Selected incoming noise-derivative experiment (2026-10-08 UTC)

Proposition: let g=V*a on LOWER coordinates, A=T(a), b=T(a*phi),
U=T(a*phi^2), N=A*U-b^2 and X=lift(A)*phi-lift(b). At arbitrary-insertion
Haar-carrier strength, test the division-free identity
A*J(N)-N*J(A)=I[K*((J_in g)*X^2+2*g*lift(A)*X*J_in(phi))].
The input/output derivatives are distinct. The actual kinetic K and complete
spatial action V remain. Available inputs: original product-heat angular
commutation, exact Leibniz rules and ordered-head lifted-factor pullout.
No positivity, marginal inverse, exact source ratio, stationarity or derivative
sign is assumed. This is a new nonlinear noise moment, not the existing
linear score-source pin.

SAME-object consumer: `QuaternionHaarPairedHessianTrace.
finite_reciprocal_paired_hessian_ibp_le` retains J(F), F=Vbar^2*N.
The predicted identity rewrites A*J(F) as
F*J(A)+2*A*Vbar*J(Vbar)*N+Vbar^2*Q, where Q is the actual incoming moment
above. It exposes a favorable negative marginal-score square, the original
spatial cross term and the COMPLETE signed incoming source cross term.
These cross terms must still be controlled relative to the surviving form;
the identity itself does not supply the missing estimate.

Prediction: exact carrier identity from three transported moment jets and
a single quadratic residual expansion. Revise if an output derivative is
confused with an input derivative, lifted factors cannot be pulled through
the actual head integral, or required strength is reduced to unit testing.
One bounded Sol implementation leaf, independent mathematical/source review,
root sole narrow compiler with fresh dynamic preflight, one 20-GiB worker
and 12-GiB reserve. No broad build/audit/guard or field changes. Parallel
read-only review tests genuine gauge-vertex Ward cancellation; individual
link derivatives of V are not assumed zero.

## Observed selected coefficient / next estimate (2026-10-08 UTC)

Classification: VERIFIED PROGRESS for the rational scaling screen;
SOURCE-LEVEL MATHEMATICAL REVIEW ONLY for the alternative-route analysis.

`lean/YMGap/Continuum/SU2QuaternionPairedPrefixCostScaling.lean`:
`normalizedPairedPrefixCost:29` defines the literal H=3*(1-w)*C(w).
`normalizedPairedPrefixCost_excess_cleared_pin:70` gives
(1+w)*(H-9)=3*(1-w)*(2*w+3).
`normalizedPairedPrefixCost_pin:100` gives the exact divided formula,
`normalizedPairedPrefixCost_excess_bounds:138` gives 0<=H-9<=9*(1-w),
and `normalizedPairedPrefixCost_lower:170` gives 9<=H.
The explicit rational error bound permits any prescribed tolerance epsilon
once 9*(1-w)<=epsilon; no CReal limit oracle or trajectory is assumed.

Final focused log `/private/tmp/ym-paired-prefix-cost-scaling-20261008b.log`
PASS: data definition axiom-free, four gates exactly {propext, Quot.sound}.
Root read the complete source and independently checked the formula/order;
parallel complete-source review found no substantive defect. The first check
failed on an extra explicit argument to eqv_symm; the one-line repair changed
no statement or limits. Failed-check sorryAx output is not proof evidence.
Checked-source SHA256:
`c690d452522a7cdd04c6239fabf87f4f66f27a61daf34f1be60659f492a08733`.
Fresh process/memory/swap preflight before both launches: 87--88% free,
zero swap, no competing Lean/Lake/pytest/runner. One 20-GiB worker,
12-GiB reserve. Root import registered, not root-built; no full-tree build,
audit/guard or baseline refresh. Canonical chart claims remain OPEN.

Decision: PRUNE smallness from the nome prefactor alone on THIS chosen
coefficient. Its bound is not a lower bound on a noise moment, actual score,
energy or signed bulk. The existing sharper adaptive cost remains available:
`lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixCurvature.lean:88`,
`prefix_frozen_curvature_adaptive_certificate`, retains radialCap(w,K+1)+2.
Do not advertise nine as an inherent obstruction to SU(2), the route, or YM.
Keep the signed terms and test the actual aggregate consumer instead.

### Parallel route reviews and exact normalization guard

No concrete useful initial padded-Wilson energy producer was found in the
inspected LocalEnergyTransport, SourceRayleighPersistence, SourceTaylor,
FiniteReferenceMargin, WidthOneSource, FringeFaceTransfer and
NoiseSurvivalObstruction modules. The conditional producers are not weakened:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalEnergyTransport.lean:224`,
`original_block_cost_le_initial_energy`, consumes its INITIAL fraction;
`lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:317`,
`Certificate.reference_ratio`, consumes accepted finite reference data.
The existing width-one inactive Wilson face has a null transmitted centered
source (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialNoiseSurvivalObstruction.lean:133`,
`origin_transmitted_pair_zero`). It cannot supply a near-unit Rayleigh floor
merely from large nome. It is not the strictly padded active source required
by the actual window; no selected-family counterexample was established.

The already checked exact cancellation is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSignedScoreEnergy.lean:170`,
`exactScoreSignedBulk_energy_split`: BOTH signed Taylor terms reassemble to
the NEXT-edge energy plus the signed finite reciprocal debt. The matched
noise is instead a PREVIOUS-step variance:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalNoise.lean:138`,
`blockNoise_variance_loss`, pins its distinct chronological square.
Incoming k and outgoing l are independent in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSignedScorePayment.lean:235`,
`exactScoreAngularBudget_terminal_signed_payment_le`.
At incoming k=0 the reciprocal/ratio definitions give zero reconstructed
source/noise, without making outgoing l's actual score/Taylor terms zero
(`lean/YMGap/Continuum/QuaternionHaarPositiveWindowInverse.lean:162`,
`reciprocal`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:213`,
`blockConditionalRatio`). Thus reconstruction and Gram slack cannot be
silently removed from a putative exact cancellation. This is a source-level
scope test, not a new checked counterexample.

NEXT: the aggregate actual normalized cost remains the required estimate,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`. A direct NEXT-edge route must retain
the exact split in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:214`,
`clearedRayleighCost_split`:
D=Z0*E(A,phi)+boundaryDrift+signedMultiplicationCost.
With `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:267`,
`energy_identity`, the resulting PAPER reduction is
2*Cost=H_edge[edgeDensity(A)*jump(phi)^2]/Z1
        +2*(boundaryDrift+signedMultiplicationCost)/(Z0*Z1).
Every t has its OWN distinct Z0,Z1. The reconstructed phi, its support,
finite reconstruction onset and boundary drift stay explicit; no finite
stationarity or exact b/A is assumed. Controlling the aggregate of this
complete expression, or the original signed Gram expression, on the
literal OWN-centered padded scaling family remains OPEN. No new interface,
unsupplied conclusion-as-input or universal noise cap was introduced.

## Selected weak-nome cost screen (2026-10-08 UTC)

Proposition to check: for the EXISTING selected cost C=prefixCurvatureCost(w),
the THREE-paired coefficient H=3*(1-w)*C satisfies
H-9=3*(1-w)*(2*w+3)/(1+w), hence 9<=H<=9+9*(1-w) at each strict nome.
Consumer: the three constant-basis terms in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSignedScorePayment.lean:127`,
`terminalSignedGramPayment`, followed by the actual (1-w) Taylor prefactor in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:218`,
`exactScoreSignedBulk`. Inputs: the literal geometric definitions of the
existing transverse and cutoff-independent radial envelopes. This tests
whether weak nome alone makes that chosen leading coefficient small; it
does NOT test the complete signed payment, actual noise scaling, a sharper
curvature certificate, or the Yang--Mills mass-gap claim.

Predicted outcome: a nonzero limiting coefficient, with an explicit rational
error bound. Abandon or revise the prediction if the actual definitions differ.
One bounded Sol leaf, root full mathematical review, one narrow monitored
20-GiB-worker check with fresh capacity preflight and a 12-GiB reserve;
no broad build/audit/guard. The separate parallel reviews test an ACTUAL
padded-Wilson initial-energy producer and exact Ward/Taylor cancellation,
before adding any more conditional interfaces. Results below will distinguish
new checked evidence from source-level arguments.

## Observed paired Ward trace / filtered-family scope (2026-10-08 UTC)

Classification: VERIFIED PROGRESS for the trace; SOURCE-LEVEL MATHEMATICAL
REVIEW ONLY for the newly composed null-source screen below.

`lean/YMGap/Continuum/QuaternionHaarPairedHessianTrace.lean`:
`paired_gradient_mixed_pin:80`, `paired_gradient_square_pin:113` are raw
coefficient identities for two wedges sharing the SAME coordinate vector.
`paired_second_trace_carrier:172` uses arbitrary-insertion Haar IBP and
stays at carrier strength; `paired_hessian_trace_carrier:220` therefore
retains the full signed trace. `finite_reciprocal_paired_hessian_ibp_le:260`
consumes the ACTUAL successor reciprocal and yields the selected literal
negative SIX-plane derivative sum. Leading THREE-basis curvature payment
is not replaced by SIX. No radius identity, inverse or Hessian-sign premise.

Final focused log `/private/tmp/ym-paired-hessian-trace-20261008c.log` PASS;
five gates exactly {propext, Quot.sound}. Root read the full final source;
independent mathematical review found no substantive defect. Initial implicit
trace inference timeout was repaired by explicitly typed intermediate moments
and explicit carrier parameters, not a limit increase. Failed-check kernel/
axiom output is not evidence. Checked-source SHA256:
`e7ccf9b26b6daf0b13f427ef7af66bf29076258975d3babc72112e81ebabf1b1`.
Fresh capacity preflight before every launch, one 20-GiB worker/12-GiB
reserve, 87--88% free and zero swap. Root import registered only;
no broad build/audit/guard or baseline refresh. Broad chart unchanged.

### Null-source review and the actual required quantifiers

This is a PAPER DERIVATION from the cited APIs, not a newly checked theorem.
For width one, n=1,r=0 and incoming/outgoing degrees ONE, source review
predicts Vbar equivalent to 1 and A equivalent to 1 under supported Haar
tests, while the FULL spatial V remains unchanged. The finite incoming
phi_1 is alpha_in*originSource on that carrier, alpha_in>0. Thus its matched
noise is alpha_in^2 times the old noise; angular A derivatives vanish and
the Ward correction is zero. The remaining three C*noise upper payments
are positive although the actual score and complete signed bulk are zero.
This prevents inferring an arbitrary-source surviving cap from the new upper
bound; it does NOT refute the bound itself.

Source pins checked by read-only review:

- `lean/YMGap/Continuum/BF4ExactSlabWidthOneGeometry.lean:75`,
  `activeSpatialFaces_one`;
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveSpatialWeight.lean:140`,
  `spatialFringeMass_haar_active`;
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveTransfer.lean:87`,
  `original_transfer_haar_active`;
  `lean/YMGap/Continuum/SU2QuaternionProductHeatConstant.lean:59`,
  `productMap_one`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeFaceTransfer.lean:133`,
  `spatial_fringe_face_moment`, and
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:64`,
  `marginalMoment_pin`, supply the OWN-center identification in the review.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialNoiseSurvivalObstruction.lean:253`,
  `origin_weighted_noise_positive`, and
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNullScore.lean:198`,
  `origin_exactScoreAngularBudget_zero`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNullScore.lean:208`,
  `origin_exactScoreSignedBulk_zero`, are the existing positive-noise and
  zero-ACTUAL-score/bulk facts. These are not themselves the new phi_1 pin.

The scope check changes the next target, not a canonical field:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNullScore.lean:181`,
`origin_transmitted_null`, annihilates this
particular incoming source after one transfer. Further filtering r>=1 then
annihilates its incoming numerator, finite phi_k and matched noise on the
carrier; that propagation is part of the paper review, not a new proof.
Do not confuse the historical accumulated blockNoise with this matched
reconstructed noise. No counterexample on the filtered range is established.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceRayleighPersistence.lean:266`,
`sourceRayleigh_floor_persists`, CONSUMES an initial floor (it produces
neither a positive floor nor a positive initial norm).
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalEnergyTransport.lean:224`,
`original_block_cost_le_initial_energy`, similarly consumes its useful
initial-energy fraction. Both allow zero filter length in their statements.
The actual backward consumer is
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`,
`original_window_budget_macro_ratio`: its hbudget concerns the eventual
literal original window, not a universal arbitrary-source noise cap.

Decision: target the literal filtered, OWN-centered padded source and complete
signed cost along its justified family, preserving initial floor/energy
obligations as OPEN. Do not reinstate the refuted universal cap, extrapolate
the r=0 witness to later filters, or treat the source-specific producer as
supplied. The actual spatial/noise Ward derivative, incoming errors and BOTH
Taylor remainders still need their useful combined estimate. All physical/
continuum/OS/full QFT/every-group/Clay claims remain OPEN; no chart reprint.

## Selected trace join and decisive null-source screen (2026-10-08 UTC)

Trace proposition: the mixed paired-gradient product is the SIX-plane
product at raw coefficient strength, by bilinear polarization of two
decomposable wedges sharing the SAME coordinate vector. Haar IBP under
arbitrary insertions then identifies the THREE paired second trace with
the SIX-plane second trace at carrier strength. Together these identify
the entire signed Hessian trace. Consumer: the current matched THREE-row
Gram payment and the checked one-plane finite reciprocal Ward estimate;
leading curvature cost stays THREE, not SIX. No radius premise or
self-coordinate padding collapse. A bounded reviewer leaf is inspected in
full by root and checked with fresh capacity preflight, one 20-GiB worker,
12-GiB reserve; no broad build or options increase.

Decisive screen selected in parallel: re-use the ACTUAL width-one null
source, but first pin the finite reconstructed phi rather than substituting
the older noise witness. A valid signed upper estimate need not be a useful
surviving-norm cap. Check the original incoming k=1 and outgoing l=1,
and retain full spatial V (not Vbar) in original marginal/OWN-center pins.
No sign/relative bound is claimed before those identities are verified.

Bounded consumer extension: apply the signed trace equality at literal
F*G^2, distribute the SIX-plane signed trace coefficientwise and sum the
already proved one-plane Ward inequalities. The new paired upper bound
retains the NEGATIVE SIX-value sum of H[A*G^2*Dij(A)*Dij(F)]. No new
analytic premise, radius identity or lower-floor inverse is used.

## Observed SAME global exact-score consumer (2026-10-08 UTC)

Classification: VERIFIED PROGRESS, no broad chart closure. In
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSignedScorePayment.lean`,
`constantPairedBasis:62`, `terminalSignedGramTerm:110`,
`terminalSignedGramPayment:127` and
`original_lastStep_terminal_signed_score_payment_le:162` compose the
SIX original reconstructed plane scores with THREE literal paired Gram
payments and SIX unchanged incoming error payments. No factor two or
leading coarse cap enters. Basis directions are constant and frozen.

`exactScoreAngularBudget_terminal_signed_payment_le:235` produces the
literal W=Vbar^2*Gout_l^2 certificate, pins the actual outgoing source and
terminal at r+1, and feeds every active row of the existing global budget.
Incoming k/outgoing l are independent. Sigma>=0 gives its nonnegative
1+sigma multiplier. No active-count ceiling replaces the signed payment.

Final focused log `/private/tmp/ym-terminal-signed-payment-20261008c.log`
PASS, five printed gates: constant basis axiom-free, four other gates exactly
{propext, Quot.sound}. Root read the full final source; independent review
found no substantive defect in both row and global consumers. One let-bound
rewrite error in the appended global consumer was repaired by explicit
`dsimp only`, not a limit increase; failed-check output is not evidence.
Source SHA256:
`4ba4e141330bb13952845855f0e9ac62e00d83aca8fa9bfe824b755f051664db`.
Fresh preflight before each check, one 20-GiB worker/12-GiB reserve,
87% free and zero swap. Root import registered only; no full build/audit/
guard or baseline refresh.

Decision: CONTINUE through the paired-to-six-plane Ward trace, then seek
a useful estimate for the combined actual spatial/noise derivative, incoming
errors and BOTH signed Taylor remainders relative to SAME surviving form.
No noise-to-surviving-square hypothesis is adopted. This global consumer
does not bound its signed payment by that surviving form. Scaling,
independent survival, completed OS, physical time/volume, SAME full QFT,
every-group and Clay remain OPEN. Broad chart unchanged, no reprint.

## Selected composition: actual SIX scores / THREE signed payments (2026-10-08 UTC)

Proposition: for the SAME original incoming source and arbitrary certified
output W, retain SIX reconstructed angular score squares, and pay their
leading sum by THREE constant paired-direction matched Gram terms, plus
SIX copies of the existing incoming error. Consumer: the existing original
angular/exact-score budget with literal outgoing reciprocal weight.
Inputs are now checked: retained leading reconstruction, matched terminal
Gram and coefficient-exact paired-square/six-square identity. No new
analytic input. Test cost multiplicity THREE, error multiplicity SIX,
constant basis (not polynomial vector-field derivatives), actual c and
finite phi_k reconstruction, arbitrary W and unchanged original action.
Abandon if a factor two, noise cap or different action/weight is smuggled
in. One bounded Sol leaf, full root review, narrow monitored check with
fresh capacity preflight, one 20-GiB worker/12-GiB reserve. The Ward trace
join and useful signed derivative/scaling estimate remain separate.

Actual consumer extension: choose the produced square weight
W=Vbar^2*Gout_l^2 and transport the last transfer outputs to the exact
existing `exactScoreAngularBudget`. Preserve every active signed row in
the finite sum, rather than replacing it by an active-count ceiling.
Incoming k and outgoing l remain independent; the existing scalar
(1+sigma)>=0 is the only additional guard. This is a direct SAME-action
consumer, not a new analytic budget assumption. Root reviews the appended
transport/sum proof and rechecks this same leaf narrowly.

## Observed matched marginal and finite Ward estimate (2026-10-08 UTC)

Classification: VERIFIED PROGRESS, no broad chart closure. The actual
positive terminal density is q*a on LOWER coordinates, not q*lift(a).
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalLocalSignedGram.lean`
now constructs its certificate, output independence and full-action pin;
`terminal_momentD_pin:455`, `terminal_momentG_pin:465` and
`terminal_local_signed_score_bound:649` retain the actual A=Ta first/all
nine ordered second jets. The final inequality is exactly the selected
matched Gram below, for supported lower phi and frozen output u.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRatioRefinement.lean`:
`original_lastStep_incomingRatio_score_reconstruction_le:282` now keeps
(1+eta)*H[W*S0^2] with S0=score(A,T(a*phi_k)); its original finite incoming
error payment is unchanged. The old `original_lastStep_incomingRatio_score_square_le:357`
retains its statement and follows by the coarse noise cap applied separately.
This supplies a signed-preserving leading consumer, unlike using the old
already-capped theorem as though its leading Hessian survived.

`lean/YMGap/Continuum/QuaternionHaarFiniteReciprocalHessianSign.lean`:
`reciprocal_multiplier_derivative_pin:63`,
`finite_reciprocal_favorable_certificate:95`,
`finite_reciprocal_hessian_ibp_le:179` prove the exact successor slope,
constructed favorable correction and weighted Hessian upper bound in one
fixed angular plane. Root and independent reviewer verified remainder
sign, successor index, factor TWO and k=0/constant-A tests. The retained
J(F) is literal, not bounded or discarded.

Final focused logs (only these scopes are claimed):

| Target | Final log | Printed gates |
| --- | --- | --- |
| LocalMarginalJets helper exports and old proofs | `/private/tmp/ym-local-marginal-api-20261008a.log` | 15 |
| TerminalLocalSignedGram | `/private/tmp/ym-terminal-local-gram-20261008c.log` | 10 |
| LastStepRatioRefinement, including old consumers | `/private/tmp/ym-score-reconstruction-retained-20261008b.log` | 8 |
| FiniteReciprocalHessianSign | `/private/tmp/ym-finite-reciprocal-hessian-20261008b.log` | 3 |

All printed dependencies are exactly {propext, Quot.sound}; no source
sorry, new axiom, classical/native shortcut or frontier-field weakening.
Initial namespace/definitional-inference and syntax errors were repaired,
not used as evidence; no option/limit was increased. Full-source root
review and independent mathematical reviews found no substantive defect.
Each compiler launch had a fresh process/memory/swap preflight, one
20-GiB worker and 12-GiB reserve, 87--88% free and zero swap. All checks
finished in their initial tool calls; no competing compiler process was
observed. Root imports registered only, no full build/audit/guard or baseline
refresh.

Checked-source SHA256, in the target order above:

```text
0f3422675902cbc5c36c01936e960284af094ec5860fe57e358b7f8ae3f02898
71b90d324aeef1e16914ffb2b095d98ba1c00400333ba197af96a74fb2bbfded
49ce0dc704023d9a4869f00f12761df0a92ea2f79417f27e7feee7e95e8a8975
3943cea591aec2756fd71cd6f1acd7f1629a6886b51b61e6fa295cc75807c97f
```

Decision: CONTINUE through actual SIX-plane reconstruction / THREE paired
Gram assembly and the Ward trace join. Then the analytic residue is the
signed derivative of the ACTUAL F=Vbar^2*N, incoming approximation errors
and BOTH signed Taylor remainders relative to SAME surviving form on a
justified scaling family. No noise-to-surviving-square bound is adopted.
The matched Gram and one-plane Ward estimate do not supply that residue.
All scaling, survival, completed OS, physical time/volume, full SAME QFT,
every compact simple group and Clay claims remain OPEN. Canonical chart
unchanged, no reprint.

The latest pasted lattice-measurement note has been re-read and independently
reconciled with the existing calibration audit/work-plan guard; no additional
correction or usable theorem input was found. No repeated literature scan,
paper list, numerical mass premise or stronger quantum Sobolev assumption.

## Selected estimate: favorable finite reciprocal correction (2026-10-08 UTC)

Proposition: for the ACTUAL finite reciprocal G=G_(k+1)(A), M=A*G,
and a certified weight F, the exact slope is
J(M)=scale(upper)*(k+1)*residual(remainder(A),k)*J(A).
The upper-window certificate produces G>=0 and residual>=0, so
F*G*J(A)*J(M) has a square certificate. In the weighted Haar identity

```text
H[F*G^2*(A*J^2(A)-J(A)^2)]
 = -H[A*G^2*J(A)*J(F)] - 2*H[F*G*J(A)*J(M)],
```

only the LAST term may therefore be discarded in an upper bound.
The actual Gram consumer uses F=Vbar^2*N. J(F) remains signed and
unbounded; this is not the refuted generic weighted-Hessian sign claim.
For three constant paired directions the leading cost occurs THREE times.
No variable-direction derivative is silently omitted.

Available inputs: literal reciprocal cancellation, successor residual
derivative, produced upper-window reciprocal/residual certificates and
angular Haar IBP on the same carrier. Test k=0 (G=scale), constant A,
F=0 and the sign convention remainder=scale*A-1. Abandon if the sign
requires an exact inverse, a Hessian premise or noise bounded by the
surviving square. The implementation starts with one fixed angular plane;
paired-direction consumption needs its own exact join.

Independent reviewer owns one bounded leaf; root reviews full source and
alone runs a narrow monitored check, one 20-GiB worker, 12-GiB reserve,
fresh capacity preflight. No broad build/audit/guard. Useful control of
J(Vbar^2*N), incoming errors and both Taylor remainders on the SAME
scaling trajectory remains OPEN.

## Selected next experiment: matched positive terminal law (2026-10-08 UTC)

Proposition: keep the produced positive LOWER terminal a in q_a=q*a,
so I(q_a*P)=A=T(a), with P the unchanged selected original output heat
packet. For a supported lower polynomial phi put b=T(a*phi),
N=A*T(a*phi^2)-b^2. Produce

```text
H[R*firstJet(u,pairedScorePlus(A,b))^2]
 <= H[R*N*(C*threeSquare(u)*A^2 + A*frozenDD_u(A)-frozenD_u(A)^2)].
```

Consumer: the literal incoming-ratio score payment and its exact outgoing
Vbar^2*G_A^2 weight, not a T1-based reciprocal. Inputs: existing terminal
certificate/support, local q/action/output-independence, original heat
curvature/windows, head differential commutation, conditional_signed_score_bound,
and actual transfer integration. Minimal algebraic API exports may avoid
duplicating the T1 proof; preserve all existing public statements. No new
analytic positivity, derivative, inverse or sign premise is allowed.

Prediction/tests: phi=0 or constant gives N=score=0; u=0; every ordered
second jet; selected output versus lower a; identical original action and
partitions. Actual arbitrary c still needs its supplied finite reciprocal
approximation/error payment, NOT an exact c/a assertion. Revise if the law
silently puts a on the output, drops an action factor, requires stronger
analytic inputs, or merely returns an unrelated Gram.

Sol owns bounded implementation and minimal reused-helper exports;
independent read-only review studies complete signed noise/spatial derivatives
and finite multiplier A*G_A-1. Root inspects full sources and alone compiles
serialized narrow targets, one 20-GiB worker and 12-GiB reserve with fresh
dynamic preflights. No broad build/audit/guard, limit rise, numerical oracle
or routine literature scan. The useful combined bound in SAME surviving
form/scaling units remains a separate analytic producer, not promised by
this selected finite join.

## Observed actual original marginal jets (2026-10-08 UTC)

Classification: VERIFIED PROGRESS. For T1=I(W), the SAME-action local
moments now satisfy coefficient-exact identities

```text
D = firstJet(u,J(T1));
G = quadraticForm(u,J_i(J_j(T1))) + C*threeSquare(u)*T1;
T1*G-D^2 = T1*frozenDD(T1) + C*threeSquare(u)*T1^2 - frozenD(T1)^2.
```

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalMarginalJets.lean`:
`frozenMarginalFirst:70`, `frozenMarginalSecond:74`,
`local_momentD_pin:464`, `local_momentG_pin:473`,
`localSignedFisher_marginal_pin:497`, `lastStep_local_differential_gram:516`.
All nine ordered jets remain, u is not differentiated, and q's independence
and original action factor pin are produced. The final differential Gram
uses the unchanged hypotheses and literal original residual/noise. No
analytic upper bound on its right side has been asserted.

Final focused log `/private/tmp/ym-local-marginal-jets-20261008d.log` PASS;
six printed gates exactly {propext, Quot.sound}. Checked-source SHA256:
`089d1d16ae040fd44354a86eb9aa6eb5153f76108a6ba717c29d8850f2a9b0c4`.
Independent read-only review found no substantive defect in the ordered
commutations, factor orientation or cost pull-through; root inspected the
complete source and direct Gram consumer. Initial namespace/coefficient
type errors and one deterministic implicit-inference timeout were repaired
with explicit typed intermediates, not increased limits. Failed-check
sorryAx output is not evidence; the final source introduces no sorry/axiom.
Every launch used a fresh dynamic preflight, one 20-GiB worker and a 12-GiB
reserve; 87--88% free memory and zero swap. Root import registered only;
no full-root/tree build, audit, guard or baseline refresh.

Decision: CONTINUE to the marginal/weight alignment and combined signed
estimate described below. Scaling/survival/completed OS/physical/QFT/
every-group/Clay remain OPEN. Broad chart unchanged, no reprint.

## Selected finite join: actual original marginal jets (2026-10-08 UTC)

Proposition: identify the produced local D/G with frozen first and all nine
ordered second paired derivatives of the ORIGINAL T1. Consumer:
`BF4ExactSlabFixedSpatialLocalSignedGram.lastStep_local_signed_gram`; its
signed Fisher is then an actual differential expression, not unrelated jet
data. Inputs: produced localOutputDensity independence and q*P=W, original
action integral pin, twice head-derivative commutation, and lifted-coefficient
pull-through. No new analytic hypothesis is needed for these identities.

Prediction/tests: D=firstJet(u,J(T1)); G=quadraticForm(u,J_i(J_j(T1)))+
C*threeSquare(u)*T1, including zero/constant u and every ordered i,j. Revise
if u is differentiated, a jet is symmetrized or T1 is replaced by Ta/free
heat. Sol owns one leaf; root inspects it and serializes a focused check with
one 20-GiB worker, 12-GiB reserve and a fresh dynamic preflight; independent
read-only mathematical review runs in parallel. No broad build/audit.

Next analytic decision: weighted Haar IBP retains a negative square but
also derivatives of the literal spatial/reciprocal/noise weights and u.
Positivity/windows alone do not permit dropping that remainder. Control of
the complete SAME signed expression remains OPEN; no integrated Hessian sign
or automatic Taylor cancellation is adopted as a premise.

## Observed weighted-Hessian sign screen (2026-10-08 UTC)

Classification: VERIFIED PRUNING. The literal one-quaternion witness
T=1+x0/2, Q=(1-x0)^2, J=D01+D23 has constructed certificates for Q and
the strict T windows 1/2 and 3/2, but
H[Q*(T*J(J(T))-J(T)^2)]=1/12>0. Therefore positivity/windows alone do
not justify the proposed generic nonpositive integrated-Hessian shortcut.
This is NOT a realization by the original T1 or weight, and does not refute
the complete original signed estimate, a Yang--Mills theory or Clay.

Checked declarations in
`lean/YMGap/Continuum/SU2QuaternionWeightedHessianSignObstruction.lean`:
`witnessWeight_certificate:53`, `witnessTerminal_floor_certificate:59`,
`witnessTerminal_floor_positive:69`, `witnessTerminal_upper_certificate:72`,
`witnessTerminal_first_pin:83`, `witnessTerminal_second_pin:90`,
`weightedHessian_eq_twelfth:101`, `weightedHessian_positive:108`.

Final focused log `/private/tmp/ym-weighted-hessian-obstruction-20261008d.log`
PASS; eight printed gates permitted, the floor's rational positivity gate
axiom-free. Checked-source SHA256:
`bc869bcda43f306acd136935925f71dabc6dbe219f33d8190e73f6a5b2ce7209`.
Root inspected the full source and independently verified the sphere-moment
calculation. Initial namespace/reduction errors and a false raw unpadding
claim were repaired, not used as evidence. Coefficient probes distinguish
[1,0] from [1]: the checked second jet retains its literal trailing zero,
and the Haar congruence then computes the exact compact expression. No
recursion/heartbeat/memory limit, axiom, sorry or trusted oracle was added.
Each check used one monitored 20-GiB worker, 12-GiB reserve and a fresh
process/memory/swap preflight; 87--88% free and zero swap. Root import is
registered, not root-built; no full-tree build/audit/guard or chart closure.

Decision: PRUNE generic sign-dropping; CONTINUE the matched-marginal,
complete signed-weight/error calculation and its still-missing useful
scaling bound. The prior selected experiment/review is retained below.

## Selected sign screen and marginal-alignment review (2026-10-08 UTC)

Decisive finite test: on one quaternion take T=1+x0/2, the paired J01+J23,
and Q=(1-x0)^2. Literal Haar evaluation predicts
H[Q*(T*J(J(T))-J(T)^2)]=1/12>0. The target diagnostic certifies Q as a
square and T's strict half-unit floor if available from the existing
coordinate API. This tests ONLY the proposed generic sign-dropping step:
it does not assert that these polynomials are the original T1/weight.
One small diagnostic leaf, kernel arithmetic, no external numerical oracle,
no broad test run. Abandon the generic sign step if this check succeeds.

Parallel source review narrows the next analytic consumer. The actual score
weight uses the reciprocal of A=Ta, not T1. A positive terminal a can be
retained in the density q*a; its positivity is produced by
`BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage_certificate:126`.
This is a PROPOSED marginal-alignment producer, not a checked declaration.
An incoming polynomial reciprocal still needs its actual error payment:
`BF4ExactSlabFixedSpatialIncomingScoreRelativePayment.original_lastStep_incomingRatio_relative_score_le:305`
retains width/nome caps, not uniform scaling control.

The exact matched-reciprocal calculation to preserve (not yet a new Lean
theorem) is, for frozen u and full remaining weight F,

```text
H[F*G^2*(A*DD_u(A)-D_u(A)^2)]
 = -sum_ij H[A*G^2*(J_j A)*J_i(F*u_i*u_j)]
   -2*sum_ij H[F*u_i*u_j*G*(J_j A)*J_i(A*G)].
```

The derivative of G^2 cancels the tempting negative-square bonus. The
finite multiplier A*G is not one; its derivative must remain. Existing
`QuaternionHaarConditionalScoreGradient.reciprocal_score_cleared_derivative:95`
retains this correction. A useful combined bound in the SAME surviving
form is missing. Retain actual spatial/noise/u derivatives and both signed
Taylor remainders; aligning the marginal alone does not pay that budget.

## Observed next experiment: FULL original-action local signed Gram

Classification: VERIFIED PROGRESS (2026-10-08 UTC). The selected local
residual route below now supplies an actual original-action instance, not
only a generic conditional consumer. Put I=partialHaarHeads N, W the literal
halfOpenAction 1, A0=T1, A=Ta, b=Tc, X=lift(A)*c-lift(b)*a. At a selected
active output slot s, use the paired frame at N+s and frozen lifted output
coefficients u. Then

```text
P=heatAt(N+s,s), q=remaining kinetic factors*(spatialWeight*liftN(1));
q*P = W, I(W*X)=0;
d=sum_i liftN(u_i)*J_i(P);
ddAug=sum_ij liftN(u_i)*liftN(u_j)*J_i(J_j(P)) + C*|liftN(u)|^2*P;
D=I(q*d), G=I(q*ddAug), V=I(W*X^2);
score=sum_i u_i*(A*J_i(b)-b*J_i(A));
H_N(R*A0*score^2) <= H_N(R*V*(A0*G-D^2)).
```

The selected packet is reversed ONLY by the checked coefficient symmetry.
The entire direction, all first and all nine ordered second jets travel
through the same explicit pair chart. The reverse certificate uses supported
Haar-carrier inverse transport, not raw coefficient equality of padded caps.
The same `prefixCurvatureCost(w)` and `prefixFrozenCurvatureCutoff(w)` are
retained. No dimension, volume, direction or inverse-floor loss enters the
cost; its nome dependence is explicit, NOT a near-one/scaling-uniform claim.

The full density is produced positive at the original head cutoff. Its
selected-output independence uses the original active-list nodup, and its
coefficient-exact reconstruction preserves every other kinetic factor, the
complete spatial weight and lifted unit. Arbitrary lower-supported a,c need
no positivity or quotient representation. The existing actual mean-zero pin
supplies the determinant specialization, without an extra marginal multiplier.
R has only its certificate, no support/independence premise. Zero and
proportional sources are admitted; no strict noise hypothesis is used.

### Exact checked declarations and verification boundary

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `pairedDerivativeAt_supported/carrier`, `chain_pairedDerivativeAt`, `chain_pairedSecondAt` | `lean/YMGap/Continuum/SU2QuaternionPairedFrameAt.lean:59`, `:71`, `:105`, `:126` | `/private/tmp/ym-paired-frame-at-20261008c.log` |
| `frozenCurvatureAt_supported`, `chain_frozenCurvatureAt`, `heatAt_frozen_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatAtFrozenCurvature.lean:72`, `:116`, `:170` | `/private/tmp/ym-paired-heat-at-curvature-20261008b.log` |
| `zero_mean_momentDeterminant_pin`, `conditional_zero_mean_signed_score_bound` | `lean/YMGap/Continuum/SU2QuaternionConditionalZeroMeanSignedGram.lean:39`, `:96` | `/private/tmp/ym-zero-mean-gram-20261008.log` |
| `lastStepAction`, `action_integral_pin`, `plane_score_integral_pin`, `paired_score_integral_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepPairedScorePin.lean:54`, `:58`, `:122`, `:159` | `/private/tmp/ym-last-step-paired-score-20261008c.log` |
| `localOutputDensity_supported/certificate/independent/action_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalOutputDensity.lean:69`, `:79`, `:89`, `:102` | `/private/tmp/ym-local-output-density-20261008.log` |
| `local_paired_score_integral_pin`, `local_frozen_score_integral_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalPairedScorePin.lean:139`, `:196` | `/private/tmp/ym-local-paired-score-20261008b.log` |
| `lastStep_local_signed_gram` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalSignedGram.lean:114` | `/private/tmp/ym-local-signed-gram-20261008c.log` |

Seven final focused targets/22 printed gates, all within {propext, Quot.sound}.
Root inspected complete final sources; independent mathematical review found
no substantive defect. No source sorry/custom axiom/classical/native shortcut,
frontier weakening or baseline refresh. Early checks failed missing namespace
opens, an incompletely rewritten chart product, a misassociated transitivity
chain and unfolding of large action definitions. Local irreducibility of the
existing action factors resolved the deterministic heartbeat timeout without
raising memory or heartbeat limits. Failed-check outputs are not evidence.

Every launch had a fresh dynamic process/memory/swap preflight. One capped
20-GiB worker, 12-GiB reserve, 87--88% free and zero swap; all checks finished
in their initial calls. Root imports are registered, NOT root-built. No
full-tree audit/build/guard or broad chart closure was run/claimed.

Final checked-source SHA256:

- `SU2QuaternionPairedFrameAt.lean`: `bde06a8062e1b83ce367b36d02a4afad40e8b54e9f0c9f1a15c7b40d15e24b8f`
- `SU2QuaternionPairedHeatAtFrozenCurvature.lean`: `c58f0c2e3fb2d3203d210b1ef30a71e8354cb9c1c4f0e8b944bf1623e5307e92`
- `SU2QuaternionConditionalZeroMeanSignedGram.lean`: `5bbc4b3d0e922f579d3f88ce8a697167ce8c891cba32b6088ddecb3aec5abcfb`
- `BF4ExactSlabFixedSpatialLastStepPairedScorePin.lean`: `dcb128c072a64a483df6c2d513ff0bb2f26cf3187d5cd186dadd57d84fde42e6`
- `BF4ExactSlabFixedSpatialLocalOutputDensity.lean`: `4dbb76ac287d19004b88385357fd7b02015566397a85b4d46639175a7371b217`
- `BF4ExactSlabFixedSpatialLocalPairedScorePin.lean`: `ee0b8127fb300b2203cb3f2611b5723be34f5e7e1e32384636836ebfa3668317`
- `BF4ExactSlabFixedSpatialLocalSignedGram.lean`: `b834092ba717df62aeecc11b3eef87568069b14f4292bb107fa6771b86a19925`

### Decision: continue, with a smaller finite residue and an OPEN analytic one

The action, source score and arbitrary-block curvature join selected below
is now constructed. D/G remain PRECOMPUTED local jet moments; no declaration
in this increment pins them to frozen derivatives of T1. The next finite
producer should prove D=firstJet(u,J(T1)) and
G=quadraticForm(u,J_i(J_j(T1)))+C*threeSquare(u)*T1. Existing output
independence, exact action pin, head-derivative commutation (twice) and
lifted-coefficient pull-through supply the inputs. This is NOT the square of
a variable-coefficient vector field, which would differentiate u.

Then the genuinely missing estimate is useful control of the SAME signed
Fisher/noise expression in the existing exact-score budget, with its actual
source/error, width, cutoff and scaling parameters. The Gram does not
produce that control or an every-state gap. The marginal is T1, NOT Ta.
Independent survival, completed OS, physical time/volume, SAME limiting QFT,
every compact simple group and Clay remain OPEN. The canonical displayed
claims did not change, so there is no chart reprint.

## Selected next experiment: original centered residual, local output frame

Decision (2026-10-08 UTC): use the already constructed paired residual
X=lift(Ta)*c-lift(Tc)*a under the FULL one-step action W, rather than
requiring a representation c=a*phi. Its existing head-integral mean is zero.
The three-moment determinant therefore predicts the sharper cleared bound

```text
T1*S^2 <= I(W*X^2) * (T1*G-D^2),
T1=I(W), D=I(frozen first output jet of W),
G=I(frozen second output jet of W + C*threeSquare(u)*W).
```

The mean-zero specialization uses `conditional_determinant_nonnegative`,
not the centered-score consumer that would add another marginal multiplier.
The existing mean and square pins are in
`BF4ExactSlabFixedSpatialLastStepScoreVariance`; its local mixed score pin
is to be exposed for the actual paired output frame. This preserves arbitrary
lower-supported a,c, with no positivity or quotient premise on either source.

Root's remaining experiment is to expose heatAt(s,N+s) as a local factor,
recode the produced original-prefix curvature to OUTPUT block N+s, and
retain all other kinetic factors, the spatial action, and the literal lifted
unit in q. Existing factor selection, certificates and output independence
are available; no whole-product tensorization is required for this local
bound. Frozen coefficients stay outside differentiation. The signed Hessian
is that of T1, NOT Ta, and stays an integrated correction rather than an
assumed nonpositive input.

Decisive tests: a=0 or c=0; proportional sources; constant frozen direction;
all nine ordered jets; unique selected active factor; correct output block;
literal halfOpenAction normalization. Revise if q still depends on that
output block, if a derivative acts on frozen coefficients, or if the action
or its unit padding is silently replaced. Verify only focused leaves with
one capped 20-GiB worker and a fresh dynamic preflight at each launch.
Sol implements the two bounded algebra/score pins in parallel; root retains
source review and serialized compilation. This is a selected finite
experiment, NOT a proved full-action bound or OS/scaling/Clay closure.

The user's lattice-measurement note is already reconciled in
`RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` and the live plan. No new
numerical premise or research branch is needed: the local estimate must still
meet SAME-operator OS reconstruction, physical time and all-state control.

## Observed three-replica signed conditional jet Gram (2026-10-08 UTC)

Decision: pursue the polynomial-valued conditional join directly. A rational
full-Haar centered Schur bound would not itself cancel a surviving polynomial
marginal. The chosen proposition is arbitrary-certified-insertion positivity
of the SAME conditional determinant N*F-S^2, with the signed Hessian retained.
Available inputs: produced original-prefix frozen curvature; positive kernel
windows; shared-tail copy/lift/head-Fubini certificates; constructive integrated
positive-window reflection. No finite certificate-level division is assumed.

Classification: VERIFIED PROGRESS. For three copied rows with
kernel P_i, score d_i, augmented Hessian dd_i and observable f_i, put
h_i=f_j-f_k cyclically, B_i=P_j*P_k and w=sum_i B_i*d_i*h_i. The cleared
replica determinant satisfies

```text
(P0*P1*P2)*T = w^2 + sum_i (B_i*h_i)^2*(P_i*dd_i-d_i^2).
```

All three curvature witnesses construct the right side. Kernel windows
cancel the product multiplier only in Haar order. Exact shared-tail triple
integration now identifies the weighted T with six times the 3x3 moment determinant.
Multiplying the retained positive marginal A gives N*F-S^2=A*det(M), without
a polynomial marginal inverse or a strict variance premise. This is an
integrated order claim under arbitrary certified tail insertions, not a claim
that T or the divided determinant has a finite square certificate.

Pre-verification checks and revision criteria (retained experiment record):
constant/zero observable, zero heads/tail, nonzero score mean,
signed cross terms and exact factor SIX; preserve the actual input action in
each copy and all shared survivors. Verify narrow leaves serially with one
20-GiB worker/fresh dynamic preflight, no full audit. Revise if replica copies
share an integrated head, an insertion is lost, positivity is assumed for the
target determinant, or an actual positive-kernel window is unavailable. The
remaining original product/domain-jet recoding and incoming-source residual
must still meet this producer; no OS/scaling/Clay claim changes.

### Constructed output and its exact boundary

With I the ORIGINAL ordered-head integral, define A=I(qP), b=I(qP*phi),
D=I(qd), v=I(qP*phi^2), e=I(qd*phi), G=I(qddAug). The checked output is

```text
N=A*v-b^2, S=A*e-b*D, F=A*G-D^2;
H_tail(R*S^2) <= H_tail(R*N*F).
```

The input density q and tail insertion R have explicit square certificates;
R has NO support or independence premise. The actual marginal A is produced
positive by head integration and retained as a spectator. Neither A nor N
is assumed strictly positive or inverted. Copies of constant caps are
identified only by supported Haar-carrier equality, not false raw coefficient
equality. The exact factor SIX is cancelled as a positive rational, not an
analytic loss. Zero heads/source and constant observables are admitted by
the general statements; independent source review checked these boundaries.

The literal ORIGINAL-prefix consumer constructs its curvature and windows
from the prior producers, with ddAug=dd+C*threeSquare(u)*P and the named
fixed-nome onset. No Hessian sign, curvature bound or target Gram inequality
is a premise of that consumer. The polynomial cost stays INSIDE G.
The precomputed paired-jet moments D/G are NOT identified with derivatives
of the marginal A when q or coefficients depend on integrated heads. This
is an actual finite conditional jet-moment inequality, not yet the full
interacting-action score estimate or an arbitrary incoming c=q*phi claim.

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `cleared_replica_pin`, `cleared_replica_certificate`, `centered_difference_pin` | `lean/YMGap/Continuum/QuaternionHaarClearedThreeGram.lean:89`, `:117`, `:153` | `/private/tmp/ym-cleared-three-gram-20261008.log` |
| `positiveFromLowerWindow`, `multiplyPositiveWindows` | `lean/YMGap/Continuum/QuaternionHaarCertifiedPositiveWindowProduct.lean:44`, `:58` | `/private/tmp/ym-positive-window-product-20261008c.log` |
| `copy_add`, `copy_neg`, `copy_cap_carrier` plus eight unchanged regression gates | `lean/YMGap/Continuum/SU2QuaternionMultiHeadVarianceReplica.lean:320`, `:325`, `:333` | `/private/tmp/ym-copy-cap-20261008.log` |
| `tripleCopy`, `tripleCopy_mul/add/neg/supported/certificate`, `replica_product_three` | `lean/YMGap/Continuum/SU2QuaternionTripleHeadReplica.lean:34`, `:41`, `:60`, `:66`, `:72`, `:95`, `:122` | `/private/tmp/ym-triple-head-20261008c.log` |
| `weighted_replica_integral_pin` (plus `symTensor_integral_pin`) | `lean/YMGap/Continuum/SU2QuaternionConditionalSignedGramReplica.lean:235`, `:144` | `/private/tmp/ym-conditional-gram-replica-20261008.log` |
| `tripleKernelWindow` and its five actual copy/lift producers | `lean/YMGap/Continuum/SU2QuaternionTripleHeadPositiveWindow.lean:195` | `/private/tmp/ym-triple-window-20261008.log` |
| `conditional_determinant_nonnegative`, `conditional_signed_score_bound` | `lean/YMGap/Continuum/SU2QuaternionConditionalSignedGramOrder.lean:127`, `:200` | `/private/tmp/ym-conditional-gram-order-20261008.log` |
| `prefix_cleared_curvature_certificate`, `prefix_conditional_signed_score_bound` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixConditionalGram.lean:49`, `:81` | `/private/tmp/ym-prefix-conditional-gram-20261008b.log` |

Eight final focused targets checked; 35 printed gates within {propext,
Quot.sound}, of which 27 are new and eight are unchanged copy-module
regressions. Root inspected all final sources; independent mathematical
review found no material defect. No source sorry/custom axiom/classical/
native shortcut, weakened field or baseline refresh. Every launch followed
a fresh dynamic preflight; one capped 20-GiB worker/12-GiB reserve, 85--88%
free and zero swap. All checks finished in their initial calls. Root imports
registered, not root-built; no full-tree audit or broad chart closure.

Final checked-source SHA256:

- `QuaternionHaarClearedThreeGram.lean`: `135ae6259a0612f5bdacba975767028e661cd5495ec9d0e0589fb08d18579f04`
- `QuaternionHaarCertifiedPositiveWindowProduct.lean`: `6f7a2038de1a31e0184126435e3ae939085cd8629cce5c9b1b9bdda07d853485`
- `SU2QuaternionMultiHeadVarianceReplica.lean`: `085355d57658e5c281232ae272b467bdc28729c1063f978fafd141819035288b`
- `SU2QuaternionTripleHeadReplica.lean`: `eb686b085c1c54faead901e2e634e8ca1b8150e21f6bc910dae63b9393b1e112`
- `SU2QuaternionConditionalSignedGramReplica.lean`: `1e27690b1e8f0fc4229b2891cc5329aded4915bc25d82d8f7360e5ae488e1566`
- `SU2QuaternionTripleHeadPositiveWindow.lean`: `3b3ef82fc163fa5a79e9a9e45f6fb19ea3e80cc4d750858ccddfe424fb300363`
- `SU2QuaternionConditionalSignedGramOrder.lean`: `c1fc774293f0de15cdd0392aa633676752b92d8d21ffadb96b31e811aa52196d`
- `SU2QuaternionPairedFrozenHeatPrefixConditionalGram.lean`: `fbb8c00a9a0d1f34db0f49237f80d4f54f6a3378944a126377fce2bac9533319`

NEXT: actual product/domain-jet recoding, exact original source/derivative
identifications and incoming reconstruction residual, then useful signed
norm comparison on a justified scaling family. Do not replace this sharper
Gram by historical-noise domination or infer a marginal-derivative pin from
bare integration. The lattice-measurement note remains research context
only, with corrections in `audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`.
All survival/OS/physical/QFT/every-group/Clay obligations remain OPEN.

## Observed signed integrated ORIGINAL-prefix Gram (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS, without asserting an integrated Hessian sign.
The existing positive-window order reflection completes the square on the
SAME kernel/background, removes its actual positive kernel multiplier, and
retains the second-jet correction in the discriminant. The unchanged
sign-dependent theorem remains intact; its stronger signed precursor is now
public and consumed by the produced full original-prefix curvature.

For p=pairedPrefix(w,K), d=sum_i u_i*Ji(p), dd=sum_ij u_i*u_j*JiJj(p),
R=sum_i u_i^2 and C=prefixCurvatureCost(w), the ACTUAL consumer proves

```text
H(background*d*f)^2 <= H(background*p*f^2) * H(background*(dd+C*R*p)).
```

For polynomial u, R is kept INSIDE integration, never pulled out as a scalar.
Coefficients are frozen; all nine mixed jets remain actual. The actual
prefix floor gives lower window m, and the produced interval enlarged to
prefixValueCap+m gives the upper window. Its positivity/order is proved.
The exact zero-lambda curvature pin consumes the checked prefix certificate.
No curvature or nonpositive-Hessian premise is supplied by the caller.
The background certificate and supported test ARE explicit premises.
This is full Haar, not a construction of the original normalized partial
conditional law or an instantiation of its complete interacting action.

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `curvature_signed_dual_bound` (plus unchanged `curvature_dual_bound` regression gate) | `lean/YMGap/Continuum/QuaternionHaarCurvatureDualBound.lean:180`, `:148` | `/private/tmp/ym-oct7-signed-curvature-dual1.log` |
| `prefix_augmented_curvature_pin`, `prefix_signed_gram_bound` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixSignedGram.lean:60`, `:89` | `/private/tmp/ym-oct7-original-frozen-signed-gram2.log` |

Two further focused checks/four printed gates within {propext, Quot.sound},
including the unchanged dual theorem. Root inspected the final source;
independent read-only scope review found no material defect. No source
sorry/new axiom/classical/native shortcut, field weakening or baseline
refresh. Fresh dynamic preflights, one 20-GiB worker, 12-GiB reserve,
87% free and zero swap. Root import registered, not root-built; no full-root/
tree audit or broad chart change. Final checked-source SHA256:

- `QuaternionHaarCurvatureDualBound.lean`: `a2f1b05a20a2b636c3d14787b532024f5496548e3da96da9e595dbb86cadab49`
- `SU2QuaternionPairedFrozenHeatPrefixSignedGram.lean`: `f58a4ff26e09716c0ed1192841d728ea43aac8f104e62e1fd3746011b058e8d6`

NEXT recode actual pairs/products as needed and assemble the original
conditional centered Gram, retaining A*F2(A)-F1(A)^2 rather than demanding
F2(A)<=0. The genuine source law/error join, coefficients pulling through
head integration and cancellation of the ACTUAL positive marginal are
still required. For arbitrary c, no silent phi=c/a. A permutation alone
also does not expose a four-link plaquette word as a two-block scalar.
All useful scaling, independent survival, completed OS, physical/volume,
SAME QFT, every group and Clay remain OPEN. No chart reprint.

## Observed full ORIGINAL-prefix frozen matrix (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS, beyond the weighted finite matrix.
The user lattice-measurement note remains research context only, with the
corrections in `audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`.
No channel measurement or finite-spacing Hamiltonian equality is a premise.

### Mathematical contraction

Write p for the ORIGINAL K-th prefix, f for the literal K+1 weighted heat,
e for its K+1 deficit and R=sum_i u_i^2. EVERY first/mixed jet is actually
differentiated before multiplying the supported polynomial coefficients u.
No derivative acts on u. The literal signed entry discrepancy is

```text
M_ij = delta_ij*C*(2*p*e-e^2)
       + p*e_ij + e*p_ij - e*e_ij
       - p_i*e_j - e_i*p_j + e_i*e_j.
curv_C(p,u)-curv_C(f,u) = sum_ij u_i*u_j*M_ij.
```

Both cross terms are retained individually, not replaced entrywise by a
symmetrized expression. No Hessian symmetry is assumed. Actual caps
U0,U1,U2 and epsilon,2*epsilon,4*epsilon construct intervals for every M_ij
with the existing scalar errorCap E. A thin three-slot adapter zero-pads
the coefficient vector into the existing six-column envelope, yielding
the PLUS certificate 6*E*R+sum_ij u_i*u_j*M_ij. Dummy matrix cells reuse
M_00; their coefficientwise-zero rows/columns contribute nothing.

Fix Cbar and the original caps BEFORE choosing epsilon. Use the existing
`errorTolerance` at precision floor m/4, m=headFloor(w). Its proved budget
gives E<=(m/4)^2, hence 6*E<=3*m^2/8<=m^2. The actual original floor
constructs p^2-6*E. Multiplication by the supported-square certificate for
R and addition to weighted curvature plus discrepancy yields curv_(C+1)(p,u).
Raising C to its fixed-nome Cbar gives cost `prefixCurvatureCost(w)`.
Factor six and the floor affect precision/onset, not this cost. No global
coefficient bound, endpoint division, inverse-floor multiplier, direction,
cutoff or carrier-size penalty. Nome dependence remains explicit.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `paired_mixed_expansion`, `mixedInterval`, `prefix_mixed_split_pin`, `deficit_mixed_interval`, `prefix_mixed_interval` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatPrefixMixedDeficit.lean:101`, `:121`, `:136`, `:144`, `:161` | `/private/tmp/ym-oct7-mixed-prefix1.log` |
| `three_polynomial_matrix_envelope_certificate` | `lean/YMGap/Continuum/QuaternionHaarThreePolynomialMatrixEnvelope.lean:142` | `/private/tmp/ym-oct7-three-matrix4.log` |
| `curvature_difference_pin`, `error_interval`, `curvature_approximation_certificate` | `lean/YMGap/Continuum/QuaternionHaarFrozenCurvatureApproximation.lean:113`, `:141`, `:180` | `/private/tmp/ym-oct7-frozen-approx2.log` |
| `prefixFrozenCurvatureTolerance`, `prefixFrozenCurvatureCutoff`, `prefix_frozen_curvature_adaptive_certificate`, `prefix_frozen_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixCurvature.lean:48`, `:53`, `:88`, `:127` | `/private/tmp/ym-oct7-original-frozen-curvature2.log` |

Four focused leaves/16 printed gates within {propext, Quot.sound}; three
printed data definitions axiom-free. Root inspected the final sources;
independent read-only review found no material defect in the exact K+1
objects, mixed order/signs, homogeneous payment or noncircular cost.
No source sorry, custom axiom, classical/native shortcut, field weakening
or baseline refresh. One capped 20-GiB worker, 12-GiB OS reserve, fresh
dynamic preflight before every compiler; 87--88% free, zero swap. Checks
finished in their initial calls. Root imports registered, not root-built;
no full-root/tree audit or broad chart closure.

Final checked-source SHA256:

- `SU2QuaternionPairedHeatPrefixMixedDeficit.lean`: `5bee092980f1de35693465eb6a03bc080ed9503b23ca080cc4c403e401f8baa6`
- `QuaternionHaarThreePolynomialMatrixEnvelope.lean`: `579a7a143de8f47dfa6990d47da1a2b167772eba3d60d23c54500ee5a15070ef`
- `QuaternionHaarFrozenCurvatureApproximation.lean`: `def545b6282a980dd1664e106dd71a2f5b55f452919b861f48f99df737363c87`
- `SU2QuaternionPairedFrozenHeatPrefixCurvature.lean`: `b278fc6c7170c4d2e402857ed28ff9305e1eeb6590eacaf73b2c12f5c449bc25`

### Next actual consumer

Establish arbitrary-block/product recoding as needed, then the ORIGINAL
interacting conditional signed Gram/Hessian join. The actual integrated
second-jet sign required by `curvature_dual_bound`
(`lean/YMGap/Continuum/QuaternionHaarCurvatureDualBound.lean:148`) is not
supplied by a free heat marginal or positivity alone. Keep every original
action factor and signed correction. No new assumed-estimate wrapper.
Useful scaling, independent survival, completed OS, physical/volume control,
SAME QFT, every compact simple group and Clay remain OPEN. Broad chart
unchanged; no reprint. Earlier sections retain their checkpoint boundaries.

## Observed full frozen weighted-heat matrix (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS, beyond separate basis-direction bounds.
Use arbitrary supported polynomial u:Fin 3->RatPoly, R=threeSquare(u),
s=frozenFirstJet(u,X). The coefficients multiply the actual jets AFTER
differentiation; no derivative acts on u. The existing
`SU2QuaternionPairedFrameScalarJets.frozenScalarSecondJet_pin`
(`lean/YMGap/Continuum/SU2QuaternionPairedFrameScalarJets.lean:211`)
already supplies the full scalar acceleration -R*X. It is reused, not assumed.

### Mathematical contraction

The actual first jets and norm relation give

```text
R*(1-X^2)-s^2 = sum_i (u cross relativeVector)_i^2.
```

Each square has original finite support and constructs a Certificate.
The mixed chain rule computes EVERY ordered JiJj before frozen contraction:

```text
frozenFirstJet(u,h) = h_x*s,
frozenSecondJet(u,h) = h_xx*s^2-h_x*R*X.
```

Both derivatives are pinned on the literal shifted finite Jacobi heat,
not independently assigned jets. The final coefficient contraction is

```text
C*R*h^2 + h*frozenSecondJet(u,h) - frozenFirstJet(u,h)^2
  = R*radial_C(h) + [R*(1-X^2)-s^2]*(h_x^2-h*h_xx).
```

The two right-hand products have constructed certificates on shared
variables. Cost C=radialCap(w,N)+delta is unchanged, with N>=1, the actual
omitted-factor onset and delta>0. No coefficient magnitude bound, unit
direction, positive direction norm, endpoint division or dimension penalty.
This is a frozen quadratic form, NOT the square of a variable-coefficient
differential operator. Scope is the WEIGHTED finite heat on original blocks
zero/one; full original-prefix matrix transport is still OPEN.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `frozen_complement_pin`, `frozen_complement_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenComplement.lean:179`, `:216` | `/private/tmp/ym-oct7-frozen-complement2.log` |
| `paired_subst_mixed`, `frozen_subst_first`, `frozen_subst_second` | `lean/YMGap/Continuum/QPolyHaarFrozenChain.lean:33`, `:99`, `:111` | `/private/tmp/ym-oct7-frozen-chain2.log` |
| `frozenHeat_first_pin`, `frozenHeat_second_pin`, `frozen_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedFrozenJacobiCurvature.lean:47`, `:54`, `:83` | `/private/tmp/ym-oct7-frozen-jacobi-curvature1.log` |

Three focused leaves/11 printed gates pass within {propext, Quot.sound}.
Root read final source; independent mathematics/source review found no
defect in ordered jets, frozen coefficient handling, normalization or the
cost. No source sorry, custom axiom, classical/native shortcut, field
weakening or baseline refresh. Fresh process/memory/swap preflight before
every compiler, one 20-GiB worker and 12-GiB reserve; 87--88% free and zero
swap observed. Final checks finished in the initial call. Root imports
registered, not root-built; no full-root/tree audit or broad chart closure.

Final checked-source SHA256:

- `SU2QuaternionPairedFrozenComplement.lean`: `cc5fcdd443f84a48aae5a3da0b9d90a25c859f5487f353abf0c00e1d2a0d815d`
- `QPolyHaarFrozenChain.lean`: `a74a8b1896bb23db28a4363c9d92d0b3c0c088f61ac867fe8b75d8ab33ee9bd7`
- `SU2QuaternionPairedFrozenJacobiCurvature.lean`: `a40cd07ad07cec5d115a77bdd9332d898668bdaac2a3111eb5b05c972c3dde04`

### Next actual consumer

Transport this full matrix to the original prefix with ordered paired
mixed deficit entries. Reuse
`QuaternionHaarSixPolynomialMatrixEnvelope.six_polynomial_matrix_envelope_certificate`
(`lean/YMGap/Continuum/QuaternionHaarSixPolynomialMatrixEnvelope.lean:134`).
Its three-slot zero padding still pays SIX times the entry cap; do not infer
entryCap*R. This conservative factor can be paid in precision/onset ONLY.
The existing public two-column producer at :74 also permits a factor-three
version by summing nine ordered pairs, but is not a necessary extra compiler.
Do not cap the coefficient polynomials globally or erase the mixed signs.
Then establish arbitrary-block recoding as needed and the ORIGINAL
interacting conditional sign estimate. These estimates and all scaling,
survival, OS, physical/volume, SAME QFT, every-group and Clay requirements
remain OPEN. Broad chart claims are unchanged; no chart reprint.

## Observed ORIGINAL-prefix paired curvature (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS. The actual weighted heat now meets the
ORIGINAL unweighted prefix through produced value and paired-jet errors.
The user lattice-measurement note remains context only, with the corrections
in `audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`. No measured channel
mass, finite-spacing Hamiltonian identification or continuum regularity is
assumed. Earlier sections below retain their checkpoint-time boundaries.

### Mathematical contraction

Let p be the original heat prefix, f the literal K+1 weighted heat, and e=p-f.
All first/second jets below are the ACTUAL paired derivatives. The proved
coefficient identity is

```text
curv_C(p)-curv_C(f)
  = C*(2*p*e-e^2) + p*dde + e*ddp - e*dde - 2*dp*de + de^2.
```

Original jet caps U0,U1,U2 and deficit caps a,b,c yield the constructed
shared-variable interval cap

```text
E = C*(2*(U0*a)+a*a) + ((U0*c+a*U2)+a*c) + (2*(U1*b)+b*b).
```

Set a=epsilon, b=2*epsilon, c=4*epsilon. First fix
Cbar=C_T(w)+geoTailBase(4,w*w,0)+1, which dominates C=radialCap(w,K+1)+1
at EVERY cutoff. Set B=Cbar*(2*U0+1)+4*U0+U2+4*U1+8 and
epsilon=divPos(m*m,B+1+m*m), m=headFloor(w). Positive denominator,
positive epsilon, epsilon<=1 and epsilon*B<=m*m are proved. The retained
nonnegative identity

```text
epsilon*B-E
  = (Cbar-C)*epsilon*(2*U0+epsilon)
      + (Cbar+8)*epsilon*(1-epsilon)
```

pays the full discrepancy. The actual original floor certificate gives p-m;
p+m=(p-m)+2m and
p*p-E=(p-m)*(p+m)+(m*m-E) construct its square payment. Add weighted
curvature, the discrepancy lower certificate and this payment to obtain
original curvature at C+1, then raise it to the fixed cost Cbar+1.
The floor is in epsilon/cutoff ONLY, not an upper-cost denominator.

`prefixCurvatureCutoff(w)` is the max of the original head floor cutoff,
radial onset and actual value/first/mixed deficit cutoffs. The split retains
N=K+1 exactly; the second derivative keeps all four ordered plane terms,
including A*A-A*B-B*A+B*B in the middle paired direction. No invented jet,
weighted-prefix substitution, endpoint division or caller curvature premise.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `prefix_split_pin`, `prefix_first_split_pin`, `prefix_second_split_pin` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatPrefixDeficit.lean:203`, `:209`, `:215` | `/private/tmp/ym-oct7-paired-prefix-deficit2.log` |
| `deficit_value_interval`, `deficit_first_interval`, `deficit_second_interval` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatPrefixDeficit.lean:222`, `:229`, `:241` | `/private/tmp/ym-oct7-paired-prefix-deficit2.log` |
| `curvature_difference_pin`, `error_interval`, `floor_square_payment`, `curvature_approximation_certificate` | `lean/YMGap/Continuum/QuaternionHaarCurvatureApproximation.lean:72`, `:109`, `:122`, `:151` | `/private/tmp/ym-oct7-curvature-approximation3.log` |
| `curvatureCap`, `errorTolerance`, `error_budget` | `lean/YMGap/Continuum/JacobiHeatPrefixCurvaturePrecision.lean:29`, `:81`, `:175` | `/private/tmp/ym-oct7-curvature-precision1.log` |
| `prefixCurvatureCost`, `prefixCurvatureCutoff`, `prefix_curvature_adaptive_certificate`, `prefix_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedHeatPrefixCurvature.lean:44`, `:52`, `:67`, `:101` | `/private/tmp/ym-oct7-paired-prefix-curvature1.log` |

Four focused leaves/37 printed gates pass within {propext, Quot.sound};
eight printed definitions are axiom-free. Root read final source and an
independent read-only review found no material sign, normalization,
same-object, certificate, cutoff or scope defect. No source sorry, custom
axiom, classical/native shortcut, field weakening or baseline refresh.
Every compiler had fresh dynamic process/memory/swap checks, one 20-GiB
worker and a 12-GiB reserve; 87--88% free and zero swap observed. All final
checks finished in the initial call. No concurrent compiler or full-root/
tree audit. Root imports registered, not root-built.

Final checked-source SHA256:

- `SU2QuaternionPairedHeatPrefixDeficit.lean`: `cd4c1fa91c923c8da7c4d73e6d6c04592975baa78ffdb6f11b4ff40ad0e38c13`
- `QuaternionHaarCurvatureApproximation.lean`: `2d24a4dea02bb7364797edda27c6ec3009d47d7040dd86aa8ccbb14e813b042f`
- `JacobiHeatPrefixCurvaturePrecision.lean`: `a4c3e9f0dc153c64a067d75ccff4449f7e882c899a9638c3a6ee5539ab41d686`
- `SU2QuaternionPairedHeatPrefixCurvature.lean`: `9f022be674784a0035e797843e6f49c45839b73c7263eea6bac44dec318b6a66`

### Next actual consumer and unchanged physical boundary

Produce the full frozen-direction matrix and arbitrary-block recoding
where required by the original conditional consumer. The three separate
paired-direction certificates do not bound mixed Hessian terms. Then join
the ORIGINAL interacting conditional score, retaining every action factor
and proving the actual integrated log-Hessian sign, not a free heat identity.
All-vector OS/scaling control, independent continuum survival, physical
calibration/volume/spacing control, SAME QFT, every group and Clay remain
OPEN. The nome is explicit and the cost is NOT uniform as nome approaches
one; 1-w is not an identified physical clock. Broad chart claims remain
unchanged; no chart reprint.

## Observed actual paired-heat curvature join (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS on the SAME finite weighted heat.
The lattice-mass note remains context, not an empirical mass hypothesis.
This increment produces curvature for the literal paired derivatives,
not merely an interface asking for it.

### Mathematical contraction

Let P be the EXISTING finite shifted Euler product and H=P', J=P'', K=P'''.
Appending its actual affine factor F with slope b gives positive polynomial
representatives for V=H^2-P*J, W=H*J-P*K and D=J^2-H*K:

```text
V_next = F^2*V + b^2*P^2,
W_next = F^2*W + 2*b*F*V + 2*b^2*P*H,
D_next = F^2*D + b*F*W + b^2*(H^2+3*V).
```

The actual first THREE formal jets are coefficient-pinned before these
identities are used. Positive shifted coefficients compile D into a Haar
certificate for h'^2-h*h'', where h is the ORIGINAL inverse-nome/half-
normalized finite Jacobi heat. The normalization is squared exactly.
All prefixes, including zero/one, are retained. No heat-floor inverse,
root-interlacing theorem, supplied derivative identity or limit derivative.

For the ACTUAL relative quaternion word on blocks zero/one, X is its scalar.
The three literal paired first derivatives are the NEGATIVE vector
components. Actual norm multiplicativity and the original unit-norm carrier
relation identify 1-X^2-(J_i X)^2 with the OTHER TWO component squares.
This is a constructed certificate under arbitrary original insertion
relations, not an assumed coordinate cone or a division by 1-X^2.

The finite Horner chain rule supplies the actual first and second paired
jets; the second keeps the scalar acceleration term, whose actual value is
-X under the SAME Haar carrier. The final checked polynomial contraction is

```text
C*h^2 + h*(J_i J_i h) - (J_i h)^2
  = radial_C(h)
    + (h'^2-h*h'') * [1-X^2-(J_i X)^2].
```

Both right-hand terms now have constructed certificates. The produced
`paired_curvature_certificate` has C=C_T(w)+tail_N(w)+delta for N>=1,
0<w<1, delta>0 and the existing omitted-factor onset. The floor appears
only in the radial Bernstein construction, NEVER in C. The two scalar
endpoints require no exceptional argument. This is separately for each
of the THREE original plus-paired directions, not yet a full frozen
quadratic-form/matrix estimate.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `angular_subst`, `paired_subst`, `paired_subst_second` | `lean/YMGap/Continuum/QPolyHaarAngularChain.lean:79`, `:149`, `:167` | `/private/tmp/ym-oct7-angular-chain2.log` |
| `product_discriminants_formal_pin`, `discriminants_nonnegative`, `heat_logConcavity_certificate` | `lean/YMGap/Continuum/JacobiHeatLogConcavity.lean:209`, `:313`, `:372` | `/private/tmp/ym-oct7-heat-log-concavity1.log` |
| `paired_first_jet`, `relativeScalarSquare`, `complementSquare` | `lean/YMGap/Continuum/SU2QuaternionPairedScalarSquare.lean:57`, `:76`, `:150` | `/private/tmp/ym-oct7-paired-scalar-square3.log` |
| `radial_substitution_pin` | `lean/YMGap/Continuum/JacobiHeatRadialSubstitutionPin.lean:101` | `/private/tmp/ym-oct7-radial-substitution2.log` |
| `pairedHeat_first_pin`, `pairedHeat_second_pin`, `paired_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionPairedJacobiCurvature.lean:69`, `:77`, `:109` | `/private/tmp/ym-oct7-paired-jacobi-curvature1.log` |

Five focused leaves/25 printed gates pass within {propext, Quot.sound};
four printed data definitions are axiom-free. Root read all final source;
independent reviews checked actual jet signs, normalization, zero prefixes,
carrier padding, endpoint handling and limited scope. No source sorry,
custom axiom, classical/native shortcut, field weakening or baseline refresh.
Every check used a fresh dynamic process/memory/swap preflight, one 20-GiB
worker and a 12-GiB reserve; observed 87--88% free and zero swap. All five
final checks completed at initial observation; no concurrent compiler,
full-root/tree build or audit. Root imports registered, not root-built.

Final checked-source SHA256:

- `QPolyHaarAngularChain.lean`: `36910ac5c324724ecd133a3660d10c22ed621dde115d8c85416eb9371cc6905d`
- `JacobiHeatLogConcavity.lean`: `a12064981d947b6fb85cc4072b2b536c2a1d269dd2de5cc5b95c1286dd5575b8`
- `SU2QuaternionPairedScalarSquare.lean`: `805d403482c884d0d43a0fc1d525e910da6168dafcf608c8786299ab10783a0f`
- `JacobiHeatRadialSubstitutionPin.lean`: `c22e74e641aa8307b2f3e590fa83ffd1350abe200d9d830f91251aa01f022434`
- `SU2QuaternionPairedJacobiCurvature.lean`: `eabb7d006f21a4ea616e136134e6617718fff5e01edc1c20e1e6022715100018`

### Next actual join and unchanged physical boundary

Transfer this curvature, not just a relative absolute derivative budget,
to the ORIGINAL unweighted prefix. Preserve N=K+1 using
`QuaternionHaarAllNomeHeatCertificate.prefix_eq_weighted_add_deficit`
(`lean/YMGap/Continuum/QuaternionHaarAllNomeHeatCertificate.lean:65`) and
`JacobiWeightedHeatPolynomial.shiftedHeat_subst_coeffEqv_weightedPolynomial`
(`lean/YMGap/Continuum/JacobiWeightedHeatPolynomial.lean:154`). Reuse the
existing value/first/mixed deficit producers named below; a paired second
derivative contains ALL FOUR ordered mixed terms, including the minus signs.
Pay the actual curvature discrepancy with slack using the ORIGINAL
`prefixFloorCertificate` (`lean/YMGap/Continuum/QuaternionHaarAllNomeHeatCertificate.lean:137`),
placing its dependence only in precision/onset, not the final upper cost.
These existing dependencies were source-inspected, not recompiled here.

Full frozen-direction curvature, arbitrary-block recoding, original-prefix
curvature transport and the ORIGINAL interacting conditional score remain
OPEN. No integrated log-Hessian sign follows from a free heat marginal.
All-vector OS/scaling estimates, independent nontrivial continuum survival,
volume/spacing control, physical Hamiltonian calibration, SAME QFT,
every compact simple group and Clay remain OPEN. The nome dependence is
explicit; 1-w is not an identified physical clock. Broad displayed claims
stay OPEN and unchanged; no chart reprint.

## Observed general-nome product addition and radial ceiling (2026-10-07 local; checked 2026-10-08 UTC)

Classification: VERIFIED PROGRESS. Continue the actual original-object route.
The user's measured-mass note remains context only; no channel mass,
finite-spacing Hamiltonian identification or continuum regularity assumption
has been adopted. The earlier checkpoints below retain historical boundaries.

### Mathematical contraction and actual consumer

The product angular jets now have a direct CReal with EXACT original N-th
approximants and `productAngularCutoff(w,epsilon)`, the max of the existing
derivative/prefix cutoffs at epsilon/3. The first completion is the original
UNHALVED `Rproduct`; its actual finite formal first jet equals 2*dPartial
in the limit, at the existing named derivative cutoff. The separately proved
actual value/first/angular comparisons yield

```text
Q = 2*P(x)^2*D(x),
P(1)^2*((D(1)-D(x))*P(x)^2) = 2*w*(1-x)*A(x)^2*A(1)^2.
```

P is the ORIGINAL completed Jacobi product and D is the EXISTING completion
of the literal product radial costs. No finite P_N=F_N substitution, limit
differentiation or supplied analytic identity. Completed odd boundary pins,
not a finite normalization shortcut, supply factor four. The determinant
polynomial is checked pointwise; separately completed endpoint frequencies
supply the endpoint determinant. Only rational factor two is cancelled in
the equality.

On [-1,1] the right side is nonnegative. The actual product floor gives
P(1)^2*P(x)^2>=floor(w)^4 at EVERY approximation; existing constructive
positive-factor cancellation gives D(x)<=D(1). Its actual endpoint ceiling
therefore produces D(x)<=C_T(w)=2*w/(1-w*w) for EVERY strict 0<w<1 and rational
x in [-1,1], not just the named-nome regression cases.

The original signed finite-tail theorem then gives

```text
D_N(x) <= C_T(w) + 4*w^(2*N+1)/(1-w*w),
(1-w)*D_N(x) <= 3/2,  when w^(2*N+1)<=1/8.
```

Negative omitted terms are paid; no monotonicity of the signed costs is
asserted. `radialOnset(w)=powBaseCutoff(w,1/8)` is explicit Nat data, independent
of x. It is a sufficient onset, not a claimed sharp cutoff. These actual
costs now supply the existing finite normalized heat consumer, producing
C*h^2+(1-x*x)*(h*hxx-hx*hx)-x*h*hx>=0 at C=C_T+tail_N, with original formal
heat jets and inverse-nome/half normalization. The positive floor enters
cancellation/construction only, NEVER the upper-budget coefficient.

The ACTUAL radial class polynomial now has a constructed Type-valued Haar
certificate after adding delta>0 to C, for N>=1 at the same small-factor
onset. Its literal formal jets are pinned for all rational arguments,
including both endpoints. Positive shifted heat coefficients and the actual
heat constant prove h>=floor(w); the produced strict margin is
delta*floor(w)^2. The existing strict Bernstein compiler and unit-coordinate
certificates construct the substituted witness. The floor affects the
Bernstein row, not C_T+tail_N+delta. N=0 heat is zero, so no strict margin is
claimed there. Polynomial equalities hold under arbitrary Haar insertions;
positivity is retained only for certified positive/square insertions.

### Declaration and verification evidence

| Produced declaration | Final source | Passing focused log |
| --- | --- | --- |
| `productAngularCutoff`, `productAngularCReal`, `productAngularCReal_eq_bare` | `lean/YMGap/Continuum/ThetaProductAngularCompletion.lean:42`, `:114`, `:138` | `/private/tmp/ym-oct7-product-angular-completion1.log` |
| `productFirstCReal_formal_pin`, `frequencyNumerator_eq_productCost` | `lean/YMGap/Continuum/ThetaProductRadialCompletedPin.lean:49`, `:136` | `/private/tmp/ym-oct7-product-radial-completed1.log` |
| `cleared_addition_square` | `lean/YMGap/Continuum/ThetaCompletedAdditionSquare.lean:179` | `/private/tmp/ym-oct7-completed-addition-square2.log` |
| `productRadialCostCReal_le_cap`, `productRadialCost_nome_defect_le_three_halves` | `lean/YMGap/Continuum/ThetaProductRadialCeiling.lean:100`, `:121` | `/private/tmp/ym-oct7-product-radial-ceiling3.log` |
| `radialOnset`, `heat_radial_nonnegative_at_onset` | `lean/YMGap/Continuum/JacobiHeatRadialProducedBound.lean:32`, `:77` | `/private/tmp/ym-oct7-heat-radial-produced1.log` |
| `radialHeat_floor`, `radialPolynomial_eval`, `radialPolynomial_strict_margin`, `radialCertificate` | `lean/YMGap/Continuum/JacobiHeatRadialHaarCertificate.lean:76`, `:111`, `:153`, `:182` | `/private/tmp/ym-oct7-heat-radial-haar2.log` |

Six focused leaves/37 printed gates pass within {propext, Quot.sound}; seven
printed computational definitions are axiom-free. Root read all final source;
independent review confirms same-object normalization, cutoff dependence and
positive-floor cancellation. No source sorry/custom axiom/classical shortcut,
native_decide, canonical-field weakening or axiom-baseline refresh. Earlier
failed elaborations are not proof evidence. One local composition uses an
800000-heartbeat elaboration allowance; no memory ceiling was raised. Every
launch used a fresh dynamic process/capacity check, one 20-GiB worker and a
12-GiB reserve; preflights observed 87--88% free memory and zero swap. One
yielded check was observed again about five minutes later while independent
mathematics/source work proceeded. No concurrent compiler or broad test suite,
full-root/tree build or audit. Root imports registered, not root-built.

Final checked-source SHA256:

- `ThetaProductAngularCompletion.lean`: `ce72636a37989e217a11fa83331d0dee9edb1e2442e1552e65565a75cdef8ac0`
- `ThetaProductRadialCompletedPin.lean`: `abf56b2dff2b5a37c7411ab1d6a32778b37e581c7527b60b5e26e5faef492a16`
- `ThetaCompletedAdditionSquare.lean`: `6a76bdccb2ec94e994ff7cd4fd7fb6fea7a32465caf4b138cc4349ac3d025221`
- `ThetaProductRadialCeiling.lean`: `8f6ab2baf419cc22a187b2ea0adbe0219195ca543f8e32de949aa7c71a211acc`
- `JacobiHeatRadialProducedBound.lean`: `290078f75d0e86fee595c3d027b4c1f362b0bb2ef50b089273aff2b6916430a1`

Additional final checked-source SHA256:

- `JacobiHeatRadialHaarCertificate.lean`: `6a4ef9d652a21feda8cb2a157e48e3a48848badcf00938702243ebce43af773e`

### Next real producers and boundary

NEXT sharp intrinsic/angular curvature on the actual weighted finite heat,
then transfer to the SAME original prefix and original conditional score.
Reuse EXISTING value/first/mixed angular deficits, not a new tail engine:

- `QuaternionHaarAllNomeHeatCertificate.deficitInterval`,
  `lean/YMGap/Continuum/QuaternionHaarAllNomeHeatCertificate.lean:91`;
- `QuaternionHaarHeatAngularDeficit.angularDeficitInterval`,
  `lean/YMGap/Continuum/QuaternionHaarHeatAngularDeficit.lean:142`;
- `QuaternionHaarHeatMixedAngularDeficit.mixedAngularDeficitInterval`,
  `lean/YMGap/Continuum/QuaternionHaarHeatMixedAngularDeficit.lean:302`;
- the existing original-prefix transport pattern
  `QuaternionHaarHeatMixedRelativeAngularBound.heatPrefixMixedRelativeBoundAt`,
  `lean/YMGap/Continuum/QuaternionHaarHeatMixedRelativeAngularBound.lean:136`.

These existing declarations were source-inspected, not recompiled in this
checkpoint. The old relative cap is not the new sharp curvature cap. The
mixed deficit is an actual ordered ANGULAR derivative estimate, not an
ordinary scalar pderiv^2 estimate. Radial/transverse class bounds do not
automatically furnish a full intrinsic matrix or an interacting marginal.

The ceiling depends explicitly on w and is uniform only in the scalar
coordinate. The normalized bound uses 1-w, NOT an identified physical clock.
Final completed arithmetic Equiv does not expose a new combined
coordinate-uniform Type-valued modulus. The radial Haar certificate is
constructed above; no original interacting score,
all-vector OS estimate, nontrivial continuum survival, volume/spacing control,
physical mass calibration, SAME QFT, every-group construction or Clay closure
is claimed. Broad chart claims stay OPEN and unchanged; no chart reprint.

## Observed signed numerator and completed parity-series join (2026-10-07 local; checked 2026-10-08 UTC)

The previous checkpoint's literal signed-frequency numerator and actual
parity/SAME-series joins are now supplied. The user's lattice-note review
remains context, not an empirical premise:
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`. The live plan continues
forward from original scalar objects and backward from the SAME physical
Hamiltonian requirements; a measured channel mass closes no analytic input.

### Actual mathematical contraction

Write L=(1-x*x)*D^2-x*D and F_N for the ORIGINAL bare theta prefix, not the
finite Jacobi Euler product. Actual squared signed frequencies give

```text
L(J_N) = -sum_(m,n) (m+n)^2*w^(m^2+n^2)*T_|m+n|(x),
M_N = sum_(m,n) (m^2+n^2)*w^(m^2+n^2)*T_|m+n|(x) = -2*F_N*L(F_N),
Q_N = 2*M_N+L(J_N) = 2*((1-x*x)*(F_N')^2-F_N*L(F_N)).
```

These pins hold for ALL rational w,x and N, including zero; no analytic
guard or positivity input. The actual Int identity
|m-n|^2+|m+n|^2=2*(|m|^2+|n|^2) is kernel-normalized, not truncated Nat
subtraction. Actual signed-list reflection and Cartesian factorization
produce M. Existing finite formal angular rules produce the first line.
Independent review confirms N=0 gives zero; N=1 gives M=4*w*x+8*w^2*x^2
and Q=4*w*x+8*w^2, which may be negative. No positivity is added.

The literal bare angular prefixes now form a constructed CReal with the
existing shell cutoff. The first-series completion is twice the existing
actual dSeriesCReal, pinned to the finite formal jet BEFORE any limit.
Arithmetic on these independently constructed series produces Q's CReal;
EVERY approximation is equivalent to the actual signed frequency-box sum.

The odd rectangle has actual unbalanced boundaries
O_N=2*H_N-h_N and O_endpoint,N=2*H_endpoint,N-h_endpoint,N. Both finite pins
hold at zero and retain their top term. Literal signed-prefix completions
use `oddSignedCutoff(w,epsilon)=oneSidedCutoff(w,epsilon/4)`, paying twice
the one-sided prefix discrepancy plus two boundary terms. The value and
independently completed frequency series each equal twice their ORIGINAL
one-sided completion. A finite factor four is never inserted.

Finally the ACTUAL completed value rectangle at y=1 equals F^2, and the
ACTUAL completed endpoint-frequency rectangle equals Q's constructed
value/first/angular numerator. The original paid rectangle lives at N+1
and the box at N; the rectangle's constructed Cauchy proof pays this offset
with half the tolerance. Endpoint scalar multiplication is commuted inside
the actual finite sums, not silently definitionally equated.

### Declaration evidence and verification boundary

| Declaration | Final source | Passing focused log |
| --- | --- | --- |
| `angular_add`, `angular_scale` (unchanged proofs exposed) | `lean/YMGap/Continuum/FiniteJacobiAngularComparison.lean:87`, `lean/YMGap/Continuum/FiniteJacobiAngularComparison.lean:103` | `/private/tmp/ym-oct7-angular-public-linearity1.log` |
| `joint_angular_frequency_pin` | `lean/YMGap/Continuum/ThetaJointAngularPin.lean:222` | `/private/tmp/ym-oct7-joint-angular-frequency1.log` |
| `moment_sum_factor_pin`, `moment_sum_angular_pin` | `lean/YMGap/Continuum/ThetaJointWeightedMoment.lean:92`, `lean/YMGap/Continuum/ThetaJointWeightedMoment.lean:171` | `/private/tmp/ym-oct7-joint-weighted-moment1.log` |
| `frequency_square_balance`, `frequency_box_numerator_pin` | `lean/YMGap/Continuum/ThetaJointFrequencyNumerator.lean:46`, `lean/YMGap/Continuum/ThetaJointFrequencyNumerator.lean:103` | `/private/tmp/ym-oct7-joint-frequency-numerator2.log` |
| `bareAngularCReal`, `bareAngularCReal_formal_pin` | `lean/YMGap/Continuum/ThetaBareAngularCompletion.lean:91`, `lean/YMGap/Continuum/ThetaBareAngularCompletion.lean:104` | `/private/tmp/ym-oct7-bare-angular-completion1.log` |
| `bare_first_jet_pin`, `frequencyNumeratorCReal_box_pin` | `lean/YMGap/Continuum/ThetaJointFrequencyCompletion.lean:54`, `lean/YMGap/Continuum/ThetaJointFrequencyCompletion.lean:84` | `/private/tmp/ym-oct7-frequency-completion1.log` |
| `odd_signed_boundary_pin`, `odd_signed_endpoint_boundary_pin` | `lean/YMGap/Continuum/ThetaOddBoundaryPin.lean:161`, `lean/YMGap/Continuum/ThetaOddBoundaryPin.lean:204` | `/private/tmp/ym-oct7-odd-boundary3.log` |
| `oddSignedCutoff`, `oddSignedCReal_eq_twice`, `oddSignedEndpointCReal_eq_twice` | `lean/YMGap/Continuum/ThetaOddSeriesCompletion.lean:36`, `lean/YMGap/Continuum/ThetaOddSeriesCompletion.lean:175`, `lean/YMGap/Continuum/ThetaOddSeriesCompletion.lean:190` | `/private/tmp/ym-oct7-odd-series-completion2.log` |
| `completed_value_rectangle_pin`, `completed_frequency_rectangle_pin` | `lean/YMGap/Continuum/ThetaJointRectangleCompletion.lean:97`, `lean/YMGap/Continuum/ThetaJointRectangleCompletion.lean:117` | `/private/tmp/ym-oct7-joint-rectangle-completion1.log` |

Seven new leaves and two changed leaves pass nine focused checks. All 61
printed gates in those final logs stay within {propext, Quot.sound}; fifteen
printed computational definitions are axiom-free. No source sorry, custom
axiom, classical input, native_decide, canonical field weakening or baseline
refresh. Initial failed elaborations are not proof evidence. Root read every
final source; independent review found no normalization, zero-index,
same-object or constructive-elimination defect. All runs used one 20-GiB
worker, a 12-GiB reserve and fresh dynamic capacity/process checks; observed
86--87% free memory and zero swap. No concurrent compiler/test suite, raised
limits, full-root/tree build or audit. Root imports are registered, not built.

Named angular/odd cutoffs are coordinate-uniform at each strict fixed nome,
NOT uniform in nome, coupling, spacing, physical time or volume. Final
rectangle Equiv uses the existing arithmetic CReal.cauchy thresholds solely
inside Prop. It does NOT expose a new combined, coordinate-uniform
Type-valued modulus, nor extract a modulus from Prop. No such stronger
consumer has been claimed closed.

Final checked-source SHA256; subsequent historical tables retain their
checkpoint snapshots rather than pretending to be current hashes:

- `FiniteJacobiAngularComparison.lean`: `32fcec01a53ffcf57137b8abfd8a74651d5fe67cea71f8a52dc121bb722c56c1`
- `ThetaJointAngularPin.lean`: `836cf0f500c37026d8b43fc32c3d32602b3180e9a9d6469e5eaa31645fe2422d`
- `ThetaJointWeightedMoment.lean`: `765d3800ba66a9c39e3325bd5d413ed1abb165b762f5bb60a108ba1f4fe52e06`
- `ThetaJointFrequencyNumerator.lean`: `59f4ab1f4c104cfc5ab33c74c80e486afb1cd47db06a5f0b227ebf4d3ed9413a`
- `ThetaBareAngularCompletion.lean`: `287ed43275053c976b602d86ee9b94e52a2b23cac4b61eedd54b73063e64a8e3`
- `ThetaJointFrequencyCompletion.lean`: `409fa740141a74359b6ba9d996dfaaf2184c6efb4271c3d9b5490cba8bcb1a33`
- `ThetaOddBoundaryPin.lean`: `c968a2bcaf6e955e46a9615135611c836c40cdcd744abb1e989cf0964a0a9717`
- `ThetaOddSeriesCompletion.lean`: `ed32e7b0af2de6be88fdbfa0a4b8c414a490dd7ca2d9303a7b231337a5317755`
- `ThetaJointRectangleCompletion.lean`: `4db2d7c592e2836193cc08c0fba9125277204c5027938a366aec1dbb5f54031a`

### Next actual consumer and residue

CONTINUE at the SAME Jacobi radial-cost limit, not a fresh assumed curvature
interface. The actual finite `FiniteJacobiAngularComparison.productRadialNumerator_pin`
in `lean/YMGap/Continuum/FiniteJacobiAngularComparison.lean:290` identifies
the cleared product numerator with P_N^2*D_N. Join its value/first/angular
limits to the constructed numerator above using the EXISTING comparison
cutoffs and actual `JacobiProductRadialLimit.productRadialCostCReal` in
`lean/YMGap/Continuum/JacobiProductRadialLimit.lean:131`. The product's literal
angular completion/SAME-product cost pin remain required; a finite comparison
alone is not that producer. Then combine with the actual completed
alternating determinant squares to obtain the cleared addition identity
and useful whole-interval ceiling. Stop/revise on any coefficient,
normalization, original-object or cutoff mismatch. Do not replace finite
bare F_N by finite Euler P_N or differentiate a value limit.

The full addition/whole-interval ceiling, strict Haar/original conditional
join, useful signed-cost/scaling estimate, independent AF survival,
all-vector completed OS comparison, physical/volume control, SAME limiting
QFT, every compact simple group and Clay remain OPEN. The canonical broad
chart is unchanged; no reprint.

### Conflict-free remote integration

The push encountered newer R1 commits through `d5291102`. They were fetched
and merged without a force push; both additions to root imports/status were
preserved and the nine checked leaf hashes above are unchanged. Incoming
R1 declarations `theta_ceiling_half` and `theta_ceiling_ff` in
`lean/YMGap/Continuum/ThetaCeilingNamedNomes.lean:70` and
`lean/YMGap/Continuum/ThetaCeilingNamedNomes.lean:75` target this SAME
radial-cost limit, but only w=1/2 and w=4/5 with rational x in [-1,1]. The
general-nome addition route remains open. Those incoming files were inspected,
not recompiled or axiom-audited here; no broader verification is inferred
from the merge. The existing scope report remains authoritative for R1:
`audits/SCOPE-THETA-CEILING-NAMED-NOMES-2026-10-07.md`.

## Prior endpoint-jet and SAME-series checkpoint (2026-10-07; residue superseded above)

The actual completed alternating value and endpoint determinant squares
are now kernel-checked. This removes that specific series-completion input,
not the full theta/Jacobi-product addition or curvature ceiling. The
lattice-measurement note remains calibration context only, as recorded in
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`; no measured mass,
Sobolev regularity, area-law implication or Hamiltonian identity is assumed.

The earlier endpoint experiment below proposed a conservative factor-three
tail. The proved bound is sharper: on OMITTED cells h<=N<T=h+|k|, so both
frequencies 2*h+1 and |2*k| are <=2*T. Their squared rational difference
has absolute value <=4*T^2, not the sum of two caps. The original shell
budget and cutoff therefore pay both value and endpoint jet. The h<T guard
is load-bearing; this cap is not asserted on the whole mixed carrier.

| Declaration | Current source | Passing focused log |
| --- | --- | --- |
| `endpointCell`, `endpointCell_abs_le_cellCap` | `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:53`, `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:262` | `/private/tmp/ym-oct7-alternating-endpoint-tail2.log` |
| `endpoint_rectangle_error_le_epsilon` | `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:332` | Same mixed-tail log |
| `squareKernel_coeff_pin`, `endpointCell_sum_eq_alternating_square` | `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:157`, `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:234` | `/private/tmp/ym-oct7-alternating-endpoint-jets3.log` |
| `mixedRectanglePolynomial_endpoint_derivative`, `endpoint_rectangle_formal_jet_close` | `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:289`, `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:309` | Same endpoint-jets log |
| `endpoint_rectangle_factored_pin` | `lean/YMGap/Continuum/ThetaAlternatingEndpointRectangle.lean:109` | `/private/tmp/ym-oct7-alternating-endpoint-rectangle1.log` |
| `endpoint_determinant_square_close` | `lean/YMGap/Continuum/ThetaAlternatingEndpointJets.lean:322` | Same endpoint-jets log |
| `bareTheta_signed_pin`, `theta_box_endpoint_value_pin` | `lean/YMGap/Continuum/ThetaJointValuePin.lean:152`, `lean/YMGap/Continuum/ThetaJointValuePin.lean:283` | `/private/tmp/ym-oct7-theta-joint-value5.log` |
| `joint_coeff_pin`, `joint_angular_pin` | `lean/YMGap/Continuum/ThetaJointAngularPin.lean:101`, `lean/YMGap/Continuum/ThetaJointAngularPin.lean:160` | `/private/tmp/ym-oct7-theta-joint-angular2.log` |
| `oneSidedCutoff`, `shellPrefix_cauchy` | `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:41`, `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:173` | `/private/tmp/ym-oct7-theta-onesided-completion3.log` |
| `alternatingCReal`, `oddCReal`, `oddEndpointCReal` | `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:256`, `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:261`, `lean/YMGap/Continuum/ThetaOneSidedSeriesCompletion.lean:266` | Same one-sided log |
| `evenCReal`, `evenEndpointCReal` | `lean/YMGap/Continuum/ThetaEvenSeriesCompletion.lean:172`, `lean/YMGap/Continuum/ThetaEvenSeriesCompletion.lean:179` | `/private/tmp/ym-oct7-theta-even-completion2.log` |
| `completed_alternating_square_pin`, `completed_endpoint_square_pin` | `lean/YMGap/Continuum/ThetaAlternatingCompletedPin.lean:51`, `lean/YMGap/Continuum/ThetaAlternatingCompletedPin.lean:69` | `/private/tmp/ym-oct7-alternating-completed-pin1.log` |

The finite half-diamond value identity is reflected into actual coefficients
BEFORE formal endpoint differentiation. The endpoint rectangle is its actual
polynomial, not a substituted square. At N=1 its excess remains 10*w^6.
The literal E/H endpoint determinant is factored independently, with H
one-sided. All five CReal constructors retain their exact original N-th
prefixes. Their differences start at index min(m,n)+1: index zero is not
incorrectly bounded by the vanishing zero shell. A named Nat cutoff fills
the legacy CReal.cauchy field; no modulus witness is extracted from Prop.
Uniformity is in x on [-1,1] at named 0<w<1, NOT in nome or physical scale.

The SAME finite paid estimates now give

```text
K(x)=E(1)*H(x)-H(1)*E(x)=(x-1)*A(x)^2,
E(1)*H_endpoint-H(1)*E_endpoint=A(1)^2.
```

The second is a separately completed frequency identity; it does not claim
a derivative of a value limit. The original joint box at y=1 is pinned to
bare F_N^2, including its central one and factor two. Coefficient reflection
then gives its actual angular product-rule jet. Finite Euler P_N is never
substituted for F_N. The full signed-frequency numerator is NOT proved yet.

### Exact verification boundary

Seven new leaves and the changed mixed-tail leaf pass their focused checks.
All 68 printed gates in the eight final logs above stay within
{propext, Quot.sound}; fourteen printed computational definitions are
axiom-free. The other constructed CReal definitions carry their actual
Cauchy proofs, with permitted axiom dependencies. No new source sorry,
axiom, classical input, native_decide, field weakening or baseline refresh.
Root inspected the complete final sources; independent mathematical review
confirmed index-zero handling, normalization, signed cancellation, named
cutoffs and separate endpoint completion. Initial elaboration failures
(imports/names, parentheses, scalar congruence and implicit Nat numerals)
and the repaired omega classical leak are not proof evidence.

Final checked-source SHA256 (earlier tables retain their historical hashes):

- `ThetaAlternatingMixedTail.lean`: `167c39fe3328b3a546c387993334e5e6fd2f12457e24d0290c360cc095a01947`
- `ThetaAlternatingEndpointJets.lean`: `d1d63242df05424771bfe88cb931391f6d64b8869d685b7947fa7cd6fcfd3f66`
- `ThetaAlternatingEndpointRectangle.lean`: `0659811e74cb990482635bd8d93a93cccc285692dba9c0f1894d26dd58f106c3`
- `ThetaJointValuePin.lean`: `aac8a79b93a9056f798481faef97bd6735a858cc5d4ef991d04fd91b05065428`
- `ThetaJointAngularPin.lean`: `a9eec00d82135fd1b95011cb64f301ef584bcbec53bd238cb6780ff7930cccde`
- `ThetaOneSidedSeriesCompletion.lean`: `db7297ae26b4acaa34b9d5559e786edff7d1fbe56f8cd62115c3db760731a400`
- `ThetaEvenSeriesCompletion.lean`: `dfa3a102495553d0b87f51c65a83adcbc952643cb6a62cfa2761b3422601a02f`
- `ThetaAlternatingCompletedPin.lean`: `154da9ecf23d17281b241b7893916dbc09497033ce7c39b8d541bcc06c39944a`

All checks used the monitored launcher, one 20-GiB worker, 12-GiB reserve,
fresh capacity/process checks, 87--88% free memory and zero swap. No limits
raised, concurrent compiler, full-root/tree audit or broad test suite.
Root imports are registered without claiming a root build. The canonical
broad chart claims are unchanged; no chart reprint.

### Prior bounded experiment (now supplied above)

CONTINUE on the literal finite bare-theta frequency numerator. With
L=(1-x*x)*D^2-x*D, J_N=F_N^2 and
M_N=sum_(m,n) (m^2+n^2)*w^(m^2+n^2)*T_|m+n|(x), prove the actual pins

```text
L(J_N)=-sum_(m,n) (m+n)^2*w^(m^2+n^2)*T_|m+n|(x),
M_N=-2*F_N*L(F_N),
Q_N=2*M_N+L(J_N)=2*((1-x*x)*(F_N')^2-F_N*L(F_N)).
```

The first uses actual finite angular ODE and sum transport; the second uses
signed reflection/product-to-sum and actual Cartesian factorization. The
coefficient-pinned angular square rule is now supplied. No analytic premise
is needed for these finite steps. Prediction/test: N=0 gives zero; N=1
gives Q_N=4*w*x+8*w^2, which can be negative. Do NOT add positivity or an
Euler-product finite identity. Reuse existing exact signed-list permutations
and explicit original coefficients; revise if a coefficient or SAME-object
pin fails. Verification stays narrow, serialized and capped.

Then compose actual parity rectangle limits, explicitly pay the unbalanced
odd boundary, and join to the literal Jacobi-product value/first/angular
limits using the existing comparison cutoffs. The full addition-square
curvature ceiling, strict Haar/original conditional join, useful signed
cost/scaling estimate, independent survival, completed OS comparison,
physical/volume control, SAME limiting QFT, every group and Clay remain OPEN.

## Selected actual parity-tail join

The next finite target is the absolute discrepancy between each actual
even/odd diamond sum at cutoff N and its literal ambient rectangle
`boxIndices (N+1)`, for BOTH theta values and endpoint-frequency-square
weights. Use the exact filter partition, not a same-cutoff rectangle
identity. Omitted cells have radius T>N, and inside the ambient rectangle
T<=2*N+3. Explicit four-sector lists of length 4*T must cover every such
shell. Their actual frequency-weighted cells pay at most
`4*T^2*w^(T^2)`; unweighted cells pay less at T>=1. Thus each omitted sum
must be bounded by `finSum (fun j => 16*(N+1+j)^3*w^((N+1+j)^2)) (N+3)`.
The existing scalar tail cutoff at epsilon/2 then pays both branches.

Inputs are literal parity exponent/frequency pins and actual Chebyshev
bounds, not supplied shell-count or discrepancy estimates. Decisive cases:
N=0, T=1, both negative indices, and shifted odd endpoints. A symmetric
integer odd rectangle is NOT paired under j -> -j-1; its boundary term
must remain until a justified later join. This step does not assert the
completed addition square, a radial curvature ceiling, or an operator gap.
Verification remains root-only serialized focused safe-launcher checks,
one 20-GiB worker and 12-GiB reserve with fresh capacity checks; no limit
raises, full-tree audit, or new assumed analytic interface.

### Observed actual weighted-tail contraction

This earlier checkpoint is commit `9d094a29`; its source lines and hashes
below identify that pre-generalization version. The reused shell engine's
current source and verification are recorded in the later alternating join.

Three new serialized focused checks PASS, with 24 printed public gates
within {propext, Quot.sound}; the two budget/cutoff definitions are
axiom-free. The existing convolution leaf also passes after making its
unchanged NoDup proof public. No sorry/axiom/classical premise, limit raise,
baseline refresh or full-root/tree audit.

| Declaration | Source | Passing log |
| --- | --- | --- |
| `evenShellIndices_length`, `oddShellIndices_length` | `lean/YMGap/Continuum/ThetaParityShellEnumeration.lean:54`, `lean/YMGap/Continuum/ThetaParityShellEnumeration.lean:60` | `/private/tmp/ym-oct7-parity-shell-enumeration3.log` |
| `evenShellIndices_mem_of_radius`, `oddShellIndices_mem_of_radius` | `lean/YMGap/Continuum/ThetaParityShellEnumeration.lean:66`, `lean/YMGap/Continuum/ThetaParityShellEnumeration.lean:161` | Same enumeration log |
| `evenFrequencyCell_abs_le`, `oddFrequencyCell_abs_le` | `lean/YMGap/Continuum/ThetaParityShellWeights.lean:152`, `lean/YMGap/Continuum/ThetaParityShellWeights.lean:170` | `/private/tmp/ym-oct7-parity-shell-weights2.log` |
| `theta_rectangle_factored_pin`, `frequency_rectangle_factored_pin` | `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:394`, `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:406` | `/private/tmp/ym-oct7-parity-diamond-tail6.log` |
| `theta_box_factored_error_close`, `frequency_box_factored_error_close` | `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:424`, `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:442` | Same diamond-tail log |
| `rectangleTailCutoff` | `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:308` | Same diamond-tail log; axiom-free |
| `boxIndices_nodup` (unchanged proof, now public) | `lean/YMGap/Continuum/ThetaParityConvolution.lean:171` | `/private/tmp/ym-oct7-parity-convolution-public-nodup.log` |

Final checked-source SHA256:

- `ThetaParityShellEnumeration.lean`: `7de2b98044f1906c17369670e409a658e594e5b26609c8518c7ecefa5cb72c09`
- `ThetaParityShellWeights.lean`: `eb0201f8c80cbd8a745634d3cc5828ceb5948bc56b4fbb1f299f461037293005`
- `ThetaParityDiamondTail.lean`: `a064b42190f559b16c76d959927e3135e34ae5cd09d9369539f6540249ad79e6`
- `ThetaParityConvolution.lean`: `36af6727e975686e41a9a094ebc9e28c72821778e20b924726e231c8017d6a47`

The first enumeration attempt mishandled j=0,k=-T and casted Nat
subtraction; the final proof isolates that vertex on side 3. The final
kernel check covers N=0, T=1 and all signed indices without numerical
sampling. Independent review checked the actual range, finite injection,
factor 16, signed error and odd normalization. All launches used one
20-GiB worker, 12-GiB reserve and fresh live capacity checks (87--88% free,
zero swap). Only focused targets were checked; registering root imports is
not a root-build claim. Completed addition/whole-interval ceiling,
Haar/conditional/scaling and all Clay-facing requirements remain OPEN.

### Next selected finite target (RESEARCH, not a Lean premise)

For C_n=`ChebyshevHalfShiftProduct.halfShiftCoord n x`, consider
`A_N=sum_(n=0..N) (-1)^n*w^(n*(n+1))*C_n`,
`H_N(x)=sum_(h=0..N) w^(2*h*(h+1))*T_(2*h+1)(x)` and
`E_N(x)=sum_(k=-N..N) w^(2*k^2)*T_|2*k|(x)`.
The candidate exact finite square is

    (x-1)*A_N^2
      = sum_(h>=0,k in Int,h+|k|<=N)
          w^(2*h*(h+1)+2*k^2)*(T_(2*h+1)(x)-T_|2*k|(x)).

`halfShift_product` supplies the pairwise kernel. The selected constructive
bijective reindex uses the existing parity decoder on (n,m): the even
sector maps to (h,k) with |k|<=h; the odd sector maps to |k|>=h+1 and its
alternating sign reverses the Chebyshev difference. At this selection point
the exact bijection, alternating-sign/exponent pins and mixed omitted-sum
proof were OPEN, not supplied assumptions; they are now proved in the
observed section below. The intended rectangular difference is
`E_N(1)*H_N(x)-H_N(1)*E_N(x)`; its omitted cells have N<h+|k|<=2*N
and should be paid by the existing actual even shells. Decisive tests are
N=0 and N=1 (candidate omitted payment at N=1 is
`2*w^6*(T_3(x)-T_2(x))`), signed k and both sign sectors.

H_N is one-sided: it is HALF the balanced bilateral odd sum. Using a full
bilateral odd sum instead changes the square's coefficient to
`2*(x-1)*A_N^2`. The unbalanced rectangles in the checked theorem above
must retain their boundary term. Do not claim finite factor four or a
completed square before the corresponding tails and SAME limit joins.
Keep the next implementation to this finite producer and its shell
consumer; no new assumed positivity or frontier bundle is needed.

Selected implementation split: Sol constructs the literal Cartesian
alternating-square expansion and the explicit mixed half-diamond bijection;
root proves the actual exponent/frequency/sign transport and composes them.
The mixed omitted-cell tail can reuse the already-proved finite shell
injection by generalizing its decidable carrier, not by copying a new tail
engine or adding an assumed analytic estimate. A second bounded Sol task
will instantiate it on the actual mixed rectangle. Independent review
checks the finite map, N=0/1, signed k and the one-sided odd normalization.
The predicted finite square and its epsilon error are mathematical
propositions to prove, not supplied fields. Stop/revise if a parity sign,
truncated subtraction, cutoff domain or SAME nome/coordinate fails to match.
Verification stays root-only, serialized focused checks, one 20-GiB worker,
12-GiB reserve and fresh dynamic-capacity checks, with no full-tree audit
or limit raise. Completed series/jet composition and the actual radial
ceiling remain the downstream consumers and are still OPEN.

### Earlier actual alternating-square contraction (2026-10-07 23:26 UTC)

This is checkpoint `e02ff556`; its mixed-tail lines and hash refer to that
pre-endpoint version. Current endpoint sources and evidence appear above.

The selected finite producer and actual shell consumer PASS. The checked
square is exactly `(x-1)*A_N(x)^2` on the mixed half-diamond. The actual
rectangle factors as `E_N(1)*H_N(x)-H_N(1)*E_N(x)`, with ONE-SIDED H and
the original bilateral E; its difference from the square is paid by the
existing `shellTailCutoff(w,epsilon)`. No analytic discrepancy, sign,
reindexing, factorization or counting premise is supplied. The identity
covers all rational w,x,N; the error requires named 0<w<1 and -1<=x<=1.
Uniformity is in x, NOT in nome, volume, physical time or spacing.

| Declaration | Current source | Passing log |
| --- | --- | --- |
| `alternatingPartial_square_expansion` | `lean/YMGap/Continuum/ThetaAlternatingKernel.lean:99` | `/private/tmp/ym-oct7-alternating-kernel1.log` |
| `positiveSquare_halfDiamond_permutation`, `listQSum_positiveSquare_halfDiamond` | `lean/YMGap/Continuum/ThetaAlternatingHalfDiamond.lean:485`, `lean/YMGap/Continuum/ThetaAlternatingHalfDiamond.lean:520` | `/private/tmp/ym-oct7-alternating-half-diamond4.log` |
| `cellCap`, `finite_shell_sum_bound` | `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:40`, `lean/YMGap/Continuum/ThetaParityDiamondTail.lean:117` | `/private/tmp/ym-oct7-parity-generic-shell.log` |
| `mixed_rectangle_error_le`, `mixed_rectangle_error_le_epsilon` | `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:172`, `lean/YMGap/Continuum/ThetaAlternatingMixedTail.lean:203` | `/private/tmp/ym-oct7-alternating-mixed-tail1.log` |
| `mixed_rectangle_factored_pin` | `lean/YMGap/Continuum/ThetaAlternatingMixedRectangle.lean:104` | `/private/tmp/ym-oct7-alternating-mixed-rectangle2.log` |
| `alternatingPairCell_encodeMixed_pin`, `alternatingPartial_halfDiamond_square` | `lean/YMGap/Continuum/ThetaAlternatingMixedPin.lean:141`, `lean/YMGap/Continuum/ThetaAlternatingMixedPin.lean:174` | `/private/tmp/ym-oct7-alternating-mixed-pin1.log` |
| `alternatingPartial_factored_error_le_epsilon` | `lean/YMGap/Continuum/ThetaAlternatingMixedPin.lean:222` | Same mixed-pin log |

Final checked-source SHA256:

- `ThetaAlternatingKernel.lean`: `57146f90eea4784b0accfc8a7253561cfddb1b52e09fd494e0c0ad4dcf057257`
- `ThetaAlternatingHalfDiamond.lean`: `ce23c437090d09b02a3737ef36fdadcfd981f3b6df4f926812b901121d413fa8`
- `ThetaAlternatingMixedTail.lean`: `77dbf3f062d46e73db9ed26647aa0871a9bfbb88e0835e1f46dde31fb9e9dbb3`
- `ThetaAlternatingMixedRectangle.lean`: `97e6b16dca39607ca42d684888af515f8c8d5218db745515231fa26c623a9ab4`
- `ThetaAlternatingMixedPin.lean`: `6c18aab0241b9d6d9ba82964cc86f7f2894c7fd351b0f45da219e6a57f167a78`
- `ThetaParityDiamondTail.lean` (current generalized engine): `7a71cbc8b95736b08ff4caf44c19b1070c04bd7ca3d70a04ecd2928c9efaf536`

The five new focused leaves pass 42 printed public gates within
{propext, Quot.sound}; ten definitions are axiom-free. The existing shell
leaf passes every old gate plus its two newly public gates. Root inspected
all sources and independently checked the even/odd algebra. Read-only
mathematical review found no sign/normalization defect. N=0 gives T1-T0.
At N=1 the half-diamond is
`T1-T0 + 2*w^2*(T1-T2) + w^4*(T3-T0)`; the rectangle adds exactly
`2*w^6*(T3-T2)`. Universal checked statements cover these cases without
sampling. Both signed k branches and the odd-sector reversal are retained.

Initial cast/projection elaboration failures and an omega-on-pair/conjunction
Classical.choice leak were repaired; only the final sources/logs above are
proof evidence. The temporary isolated pair-algebra check is diagnostic,
not an additional repository proof. No new source sorry/axiom/classical
premise, canonical field change, baseline refresh or full-root/tree audit.
All launches were serialized through the safe launcher: one 20-GiB worker,
12-GiB reserve, fresh 88%-free zero-swap capacity checks, no competing
compiler and no limit raises. Root imports registered, not root-built.
Completed addition/whole-interval radial ceiling, strict Haar/original
conditional/scaling and every Clay-facing requirement remain OPEN.
The canonical broad chart state is unchanged; no reprint.

### Next selected join: endpoint jets and SAME limits (RESEARCH)

Do not differentiate the completed value identity without a derivative
producer. The required finite endpoint cell is

    w^(2*h*(h+1)+2*k^2) * ((2*h+1)^2-(2*k)^2).

Its HALF-DIAMOND sum should equal A_N(1)^2 by reflecting the proved finite
square into actual coefficient polynomials before formal differentiation.
The RECTANGLE endpoint derivative is not equal to that square at finite N:
the N=1 excess is `10*w^6`. It needs its own omitted-jet payment. For
positive radius T=h+|k|, the proposed absolute frequency difference is
at most 9*T^2; existing 4*T shell coverage then suggests a conservative
`3*omittedBudget`, and a cutoff at epsilon/3. These are propositions to
prove, NOT new inputs or assumed derivative limits.

Available inputs: `ChebyshevFormalJets.coefficients_of_eval_eqv`,
`CoeffEqv.pderiv`, `pderiv_pmul`, `pderiv_padd`, `pderiv_pscale`,
`QPoly.eval_pmul`, `eval_padd`, `eval_pscale`, and the literal mixed-tail
engine above. Build only the necessary half-shift/alternating coefficient
polynomials, not a new calculus. Downstream SAME-object residues include
the actual joint value J_N(x,1)=bareTheta_N(x)^2, the endpoint-frequency
numerator pin to its actual first/angular jets, and the product-limit join
using `Ppart_sub_bareTheta_close`, `fullProdDx_sub_two_dPartial_close`,
`productAngularJet_sub_bare_close` and `productRadialNumerator_pin`.
Keep actual prefix approximants and the existing `KPLimit.crealOfTail`
construction/moduli when composing CReal limits. Retain the unbalanced
odd boundary through this join; do not silently insert a finite factor four.

Continue this finite producer/jet route, with N=0/1 as decisive tests.
Stop/revise if finite rectangle and half-diamond jets are conflated, a
derivative is inferred merely from value convergence, or the bare theta
prefix is substituted for the finite Euler product. Verification remains
serialized focused checks under the unchanged dynamic-memory contract.
The intended addition-square curvature ceiling is still an analytic
producer to establish, not an inhabited premise.

## Mathematical selection before implementation

The previous checkpoint proves an unweighted whole-product norm-loss law
and refutes arbitrary positive output weighting. Do not reopen that shortcut.
The exact original terminal variance balance already exists, so no new
stationarity wrapper is needed.

The remaining joint-score step needs direction coefficients that depend on
the output, not just a fixed rational vector. For the six rotations at ONE
block, set Mij=h*Di(Dj h)-(Di h)*(Dj h), U=C(w)*h^2. The existing ORIGINAL
heat certificates give both U+Mij and U-Mij. The missing finite construction
is a certificate for

    6*U*sum_i ui^2 + sum_ij ui*uj*Mij,

for supported POLYNOMIAL ui. Every ordered mixed entry is retained. The
square identity

    U*(v^2+z^2)+2*M*v*z
      = ((U+M)*(v+z)^2+(U-M)*(v-z)^2)/2

constructs each pair; half-summing all ordered pairs gives the desired
six-column envelope. No coefficient is differentiated. This is the FROZEN
Hessian, not D_u(D_u h), which would add derivative-of-ui terms.

Inputs: `lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:152`,
`heatLogHessianBounds`, and the supported square/product/transport
constructors in `QuaternionHaarSquareCertificate.lean`. Existing
`SU2QuaternionProductHeatSignedLogCurvature.productHeat_signedCurvature`
uses rational constant coefficients and is not this substitution theorem.

Downstream consumer: the missing adaptive whole-product/conditional Gram
estimate for S_i=A*Di b-b*Di A. **No declaration currently implements that
complete adaptive join.** The local certificate is one needed input, not
the joint-score theorem itself. The complete original V source, paired
residual, output weight and terminal mismatch must survive the eventual
join. Do not use the equal-endpoint integrated Hessian sign on a conditional
law, and do not turn a qMax/A upper comparison into a useful spatially
uniform constant by omitting its denominator dependence.

Decisive tests: zero coefficients, signed/cross coefficients, and coefficients
depending on the differentiated output coordinate. The frozen definition
must remain valid without derivative-of-coefficient terms. m=6 is the local
number of rotations, NOT an active-block or volume count. C(w) retains its
genuine nome dependence; it is not AF-uniform.

Verification budget: root alone runs serialized narrow safe-launcher checks,
one 20-GiB worker, 12-GiB OS reserve, fresh live capacity preflights. Sol owns
only the finite envelope; root owns the actual-heat instance. Stop/revise if
the proof assumes a Hessian sign, discards action factors, imports another
carrier, requires limit raises or expands into unneeded generic scaffolding.

## Observed evidence

Three serialized focused checks PASS, with four printed declarations
depending only on {propext, Quot.sound}:

| Declaration | Source | Passing log |
| --- | --- | --- |
| `two_polynomial_envelope_certificate` | `lean/YMGap/Continuum/QuaternionHaarSixPolynomialMatrixEnvelope.lean:74` | `/private/tmp/ym-oct7-six-polynomial-matrix3.log` |
| `six_polynomial_matrix_envelope_certificate` | `lean/YMGap/Continuum/QuaternionHaarSixPolynomialMatrixEnvelope.lean:134` | Same matrix log |
| `heat_frozen_six_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionFrozenSixHeatCurvature.lean:58` | `/private/tmp/ym-oct7-frozen-six-heat2.log` |
| `lastStep_frozen_six_score_curvature_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFrozenScoreCurvature.lean:64` | `/private/tmp/ym-oct7-frozen-six-original-score.log` |

Log SHA256, in the three-log order above:

```text
7bd0e0e6892d80a6068934434af5d4f10a77abdb330f092cdb9b70a47c931a9c
f47dfd9f2d640368cdea9eb97e14c5bbc48ca17d955dbc23eab0c4a75a1c9604
67a5f852735f6f92699c2ede3aef0c887f7f68f83f75db66ff48193daed5b1a4
```

Earlier elaboration failures were a pre-import module-comment form, a missing
parenthesis and defining namespace opens; they are not proof evidence.
No limits were raised. Root and Sol inspected the finite producer; independent
read-only review found no mathematical defect in its ordered-pair identity
or the actual factor/score instance. No new sorry, axiom, classical input,
canonical field change or scorecard closure. Root import registration only;
no full-root/tree audit or hashed-baseline refresh.

Observed capacity before the last two launches: 87--88% memory free, zero swap,
no competing compiler. Every check used one 20-GiB worker and 12-GiB reserve.
The universal polynomial-coefficient type includes zero, signed and
output-coordinate-dependent coefficients; the resulting expression is
explicitly frozen, with no differentiated coefficients. No separate numerical
test or original conditional-score inequality is claimed.

## Interpretation and next decision

CONTINUE at the whole-product frozen-Hessian/conditional Gram join. The local
adaptive restriction is removed; a global estimate is NOT supplied. Preserve
cross-block terms, the original interacting source/action and output weight,
actual normalization and terminal mismatch. Do not sum copies of a global
loss at every block or infer a conditional integrated Hessian sign.

The next finite algebraic target uses frozen jets d_p=sum(u_i*Di p),
e_p=sum(u_i*u_j*Di(Dj p)), with polynomial costs R_p,R_q:

```text
d_pq = d_p*q+p*d_q
e_pq = e_p*q+2*d_p*d_q+p*e_q
(R_p+R_q)*(p*q)^2+(p*q)*e_pq-d_pq^2
  = q^2*(R_p*p^2+p*e_p-d_p^2)+p^2*(R_q*q^2+q*e_q-d_q^2).
```

This is the proposed tensorization identity, NOT a newly checked declaration.
`lean/YMGap/Continuum/QuaternionHaarProductLogCurvature.lean:30`,
`productLogCurvatureLower`, has the scalar-cost version; the required
polynomial-cost and actual frozen-derivative pins remain missing.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticMarginals.lean:118`,
`kineticWeight_eq_indexedProduct`, is the SAME-kernel consumer pin.
Local costs should add as 6*C(w)*sum_s sum_i u_(s,i)^2; product cross terms
cancel in the log-Hessian numerator, not by claiming cross derivatives vanish.

The user's lattice-measurement note is already incorporated in
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` and the live plan.
It changes no proof premise: fitted-channel masses are not every-state gaps,
and an exact discrete transfer logarithm does not bypass physical-clock or
limiting-theory identification. The SAME completed comparison, justified
scaling family, nontrivial survival and limiting QFT remain open. This local
certificate closes no broad chart node or Clay obligation.

## Next experiment: polynomial-cost tensorization

Selected target: construct the displayed product-jet identity, then instantiate
it with local frozen heat jets on the literal original product. The adaptive
coefficient restriction is already removed. The missing input here is additive
polynomial-cost assembly, not another scalar smoothing estimate.

Available inputs are the local six envelope, supported opposite-square
multiplication and the existing scalar product identity. Predicted result:
local costs add, cross products cancel exactly and no active-count multiplier
appears. Decisive tests: empty product, duplicate factors, arbitrary signed
and output-dependent coefficients. Differentiate only the heat factors, never
the coefficients. A recursive formal jet is not yet a direct differential
or conditional integral pin; keep that boundary explicit.

Verification budget remains serialized focused checks with one 20-GiB worker,
12-GiB reserve and fresh dynamic process/memory preflights. Root verifies;
Sol supplies only the finite product identity; an independent reviewer inspects
the actual join. Stop/revise if an integrated log-Hessian sign is assumed,
cross-block derivatives are dropped, source/action/output weights change or
the proposed consumer needs a missing derivative pin.

### Observed tensorization evidence

Three serialized focused checks PASS; six printed declarations use only
{propext, Quot.sound}:

| Declaration | Source | Passing log |
| --- | --- | --- |
| `polynomialJet_product_curvature_certificate` | `lean/YMGap/Continuum/QuaternionHaarPolynomialJetCurvature.lean:49` | `/private/tmp/ym-oct7-polynomial-jet-curvature.log` |
| `frozenSixHeatEnvelope_jet_pin` | `lean/YMGap/Continuum/SU2QuaternionProductHeatFrozenJetCurvature.lean:95` | `/private/tmp/ym-oct7-product-frozen-jets3.log` |
| `heat_frozen_six_jet_certificate` | `lean/YMGap/Continuum/SU2QuaternionProductHeatFrozenJetCurvature.lean:109` | Same product log |
| `productHeat_frozenJet_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionProductHeatFrozenJetCurvature.lean:153` | Same product log |
| `lastStepScoreCoefficients_supported` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFrozenScoreProductCurvature.lean:53` | `/private/tmp/ym-oct7-original-frozen-score-product.log` |
| `original_kinetic_frozenScoreJet_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFrozenScoreProductCurvature.lean:70` | Same original-score log |

Log SHA256 in the three-log order above:

```text
f9f1ae8b3fc81457d7eef94ad58958ea6932ac3648746edfc0cbbd155afd78be
7a7368679cfa73d66192262f51560fdd47fe9654aa3f743717638a693f1f4e40
079c9ac6e4340329594c57e1bdd727dfdfa99b523fc56af411bac47d662c8730
```

The first product attempt failed on a defining namespace; the second failed
because a constant-zero polynomial is not definitionally the empty zero list.
The repaired empty-product transport uses `RatPolyCoeffEqv.zero_smul`, not a
limit raise or changed claim. Those failed logs are not proof evidence.
Each launch had a fresh capacity/process preflight: 87--88% free, zero swap,
no competing compiler. No new source sorry/axiom/classical input or canonical
field change; root import registration only, no full-root/tree audit or
hashed-baseline refresh. Empty and duplicate-factor cases are in the universal
recursive theorem, not separate numerical claims.

### Interpretation and remaining exact joins

CONTINUE. The local matrix-to-heat-jet pin and additive polynomial-cost product
construction are checked, including the original kinetic base and actual
transfer-score coefficients. They do NOT yet assert that the recursive jets
equal a direct whole-kernel frozen angular sum. The missing differential pins
are precisely the first/second frozen Leibniz rules and factor localization;
coefficients must not be differentiated.

The subsequent conditional target retains the Hessian:
S_u^2 <= Noise*(R*A^2+A*F2(A)-F1(A)^2), with A=T a, and only under the
genuine positive conditional law and a justified source factorization/error
join. For arbitrary original c, do not silently set phi=c/a. The existing
incoming reciprocal/error construction remains required where appropriate.
Output coefficients must pull through head integration before this target is
an actual original-score statement. `partialHaarHeads_mul_lift` in
`lean/YMGap/Continuum/SU2QuaternionHeadChainComposition.lean:51` and
`angularDerivative_partialHaarHeads` in
`lean/YMGap/Continuum/SU2QuaternionHaarTailDerivative.lean:171` are the existing
pin inputs. Polynomial-column Gram alone does not supply the score column
F1(K)/K; a cleared square/order-reflection join is still missing.

Do NOT assume an integrated log-Hessian vanishes: free marginal cancellation
is only integral DD K=0. With full unweighted Haar and a constant angular
generator, H[h*D^2h-(Dh)^2]=-2*H[(Dh)^2]; conditional/action/output insertions
retain their own derivatives. No such sign or cancellation is imported here.

The nome cap still includes `heatSecondDerivativeCap/headFloor+relativeCap^2`
(`lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:143`,
`secondRelativeCap`, and `:148`, `logCurvatureCap`). No useful near-one-nome
or physical scaling control is supplied by additive tensorization.
The broad chart and Clay status remain OPEN and unchanged.

## Decisive parameter screen selected before further derivative scaffolding

Independent source review identified a cap issue: the current entrywise bound
uses the reciprocal global heat floor. Before investing in more differential
joins, test the conservative cleared proposition

    4224 <= (1-w)^2 * logCurvatureCap(w).

Available inputs: the EXISTING `headFloor_le_nome_defect_square`,
`lean/YMGap/Continuum/BF4ExactSlabHeadFloorNomeCeiling.lean:61`; the zeroth-term
`prefix_bound`, `lean/YMGap/Continuum/SU2HeatPolynomialPrefixBound.lean:105`;
and the literal cap formulas. This screen concerns the chosen bound only,
NOT the true optimal curvature, any noise, retained signed Hessian or YM gap.

Predicted outcome: the screen passes; additive product algebra cannot make
this cap bounded or inverse-linear in the nome defect. If confirmed, prioritize
a sharper ONE-SIDED lower-curvature producer or the complete signed-cost route
over further wrappers around this entrywise cap. Cancellation/noise estimates
are not refuted and must not be dropped. The screen is a rational theorem
with the same gate/single-worker budget, not a numerical parameter sweep.
Observed evidence: focused check PASS, three declarations within
{propext, Quot.sound}:

- `prefixBudget_one_le`,
  `lean/YMGap/Continuum/SU2QuaternionLogCurvatureCapObstruction.lean:37`;
- `heatSecondDerivativeCap_ge_4224`, same source `:46`;
- `logCurvatureCap_nome_defect_square_lower`, same source `:59`.

Accepted log `/private/tmp/ym-oct7-log-curvature-cap-obstruction2.log`, SHA256
`71baf4d2702ff7f2426971442fecaa270a8d1985f7964acff9a7e508bdf80c95`.
An earlier failed check omitted the explicit reciprocal positivity proof;
the repair supplies the existing `headFloor_positive`, with no limit raise
or changed statement. No new source sorry/axiom/classical input or canonical
field change. The same fresh preflight/single-worker limits apply; no full
audit or root rebuild.

Decision: REVISE the analytic priority toward the one-sided producer or
complete retained signed-cost estimate. Bounded direct derivative pins remain
useful algebra, but do not treat this entrywise cap alone as a scaling
producer. Do not infer a theorem about noise or surviving variance from
a theorem about the cap. Independent review confirms this distinction and
the accurate recursive-versus-direct jet boundary.

### One-sided research benchmark, not a formal input

Hamilton's original *A Matrix Harnack Estimate for the Heat Equation*,
Corollary 4.4 (pp. 125--126), bounds the covariant log Hessian of a positive
heat-equation solution below by -g/(2*t) on compact manifolds with nonnegative
sectional curvature and parallel Ricci tensor; it explicitly includes spheres.
This is a possible one-sided benchmark, not a Lean theorem or finite-prefix
certificate. Root checked the original-paper transcription; direct publisher
PDF requests returned 403.
[Original paper transcription, Corollary 4.4](https://doczz.net/doc/7681685/a-matrix-harnack-estimate-for-the-heat-equation),
[publisher record](https://doi.org/10.4310/CAG.1993.v1.n1.a6).

Our inference for a possible route: prove the constructive kernel/heat-time
identification and one-sided lower-curvature estimate, then transfer it to
the original finite prefix using an explicit value/derivative deficit and
positivity margin. None of these joins is supplied by citing the paper.

There is a frame distinction: for a frozen ambient rotation field X(x)=B*x
on the unit sphere, its tangent acceleration is B^2*x+|B*x|^2*x. Consequently
D_X^2(log h) includes the covariant Hessian AND the log-gradient paired with
this acceleration. That term must be controlled or removed by a justified
frame change, not silently omitted. Constant left-invariant SU(2) directions
are a candidate geodesic frame in a bi-invariant metric, but their exact
comparison with the existing six-rotation jets is unproved here.

Do not confuse this desired LOWER bound with the stronger Ricci-two UPPER
curvature expression already refuted at the original antipode; see
`audits/AUDIT-ORIGINAL-ANTIPODAL-CURVATURE-2026-10-03.md`. Do not claim
any curvature method succeeds or fails from this benchmark. The actual
conditional Hessian, original source/action, output weight, normalization,
nontrivial survival and all-vector limiting-theory joins remain required.

## Next selected experiment: exact paired-score frame join

Target: write the SAME coupled-score energy in three paired directions,
without changing its action, source, terminal messages or output multiplier.
For Sij=A*Dij(b)-b*Dij(A), the first-jet pin Sij=xi*Fj-xj*Fi,
Fj=A*partial_j(b)-b*partial_j(A), implies the coefficient-exact identity
S01*S23-S02*S13+S03*S12=0. Consequently

    (S01+S23)^2+(S02-S13)^2+(S03+S12)^2 = sum_(i<j) Sij^2.

The opposite-sign triple has the same energy. Available inputs are literal
angular differentiation, `conditionalScore` and polynomial ring reflection.
The actual consumer is `exactScoreAngularBudget`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreBudget.lean:112`:
retain its A=g_(n+r+1), b=T^(r+1)(g_n*psi), Vbar^2*G^2, sigma and active list.
Predicted outcome: exact equality for arbitrary supported or unsupported
polynomial A,b and arbitrary multiplier, including zero scores; no inverse,
conditional-law restriction or stationary measure is needed. This removes
the energy-conversion obstruction to trying a three-direction producer, NOT
the missing producer, geometric frame identification or conditional join.

Verification budget: two narrow serialized checks, fresh dynamic preflights,
one 20-GiB worker and 12-GiB OS reserve. Sol implements finite algebra only;
root checks it and the original consumer. Revise if a sphere/unit-radius
hypothesis is needed for the coefficient identity, weights change, or an
unproved geodesicity/heat-time/Harnack claim is used as a premise.

### Independent Jacobi test (research calculation, not kernel evidence)

The SAME positive Jacobi derivative has a better hemisphere-local estimate:
with r_k=2*w^(2k+1)/(1+2*w^(2k+1)*x+w^(4k+2)), its positive-mixture
log Hessian retains E(r_k^2)+Var(r_k). For x>=0, sum r_k and sum r_k^2
are bounded respectively by 2*w/(1-w^2) and 4*w^2/(1-w^4), with no global
Euler-floor reciprocal. Original K(V*source) is not hemisphere-supported;
there is NO supplied global sector/payment join.

The proposed all-finite-Jacobi global inverse-linear bound fails its N=2
diagnostic: the polynomial is proportional to x+a, where
a=(w+w^-1+w^3+w^-3)/4. For 1<a<=2, at x=a-2/a its invariant radial log
Hessian is -a^2/(4*(a^2-1)); a-1 is quadratic in 1-w. This is a rational
research calculation, NOT a new Lean obstruction. It does not refute a
cutoff-dependent Jacobi route or the original guarded character prefix:
their exact value/derivative deficits must be paid. Do not import this
diagnostic as a theorem about the original transfer or its physical gap.

### Observed paired-score evidence

Both final focused targets PASS, with all eight printed public dependencies
within {propext, Quot.sound}:

| Declaration | Source |
| --- | --- |
| `decomposable_plucker` | `lean/YMGap/Continuum/QuaternionHaarConditionalScorePairedFrame.lean:54` |
| `conditionalScore_firstJet_pin` | Same source `:70` |
| `conditionalScore_plucker` | Same source `:103` |
| `plusSquare_eq_sixScoreSquare` | Same source `:192` |
| `minusSquare_eq_sixScoreSquare` | Same source `:204` |
| `plusSquare_weighted_pin` | Same source `:216` |
| `minusSquare_weighted_pin` | Same source `:222` |
| `pairedScoreAngularBudget_eq_exact` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepPairedScoreBudget.lean:66` |

Accepted logs, in this order:

```text
/private/tmp/ym-oct7-paired-score-frame-clean.log
ae6df76315d15b00b6d229ab0e9559cb037ab7633be643cd063bb5733e6fa4f0
/private/tmp/ym-oct7-original-paired-score-budget-clean.log
a1dc372e913053121744f42baa37fc4ebadb92626b2812e3b6014f0a16403007
```

The first frame compilation passed elaboration but FAILED the axiom gate:
private dependent finite-index congruences brought `Classical.choice` into
the energy identities. Intermediate axiom prints localized the dependency;
direct congruences at literal slots 0,1,2 removed it. The old and localization
logs are NOT accepted proof evidence. The initial original consumer also
failed on a missing defining namespace, subsequently supplied without changing
the statement. No new source sorry/axiom/classical input or limits change.
Fresh preflights before every launch showed no competing compiler, 87--88%
free and zero swap; checks ran sequentially with one 20-GiB worker and 12-GiB
reserve. Root registration only; no full-root/tree audit or baseline refresh.

Decision: CONTINUE with the exact three-score currency, NOT a geometric or
Harnack claim. The energy conversion is now proved for the original budget,
including zero/arbitrary sources and signed multipliers. Constructive frame/
heat identification, the genuine one-sided bound, actual conditional law,
normalization, retained signed cost and all scaling/Clay joins remain OPEN.
The user's lattice-measurement note remains incorporated in the existing
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` and work-plan priority;
it supplies no numerical premise for this proof. No routine listing scan or
duplicated literature review was needed. The canonical broad chart is unchanged.

Independent read-only source review found no semantic issue: each triple
alone retains the original six-score energy without a radius/factor-two
correction, and the actual consumer adds no source-support, nonzero-source
or positive-sigma premise. It confirms the algebra-versus-geometric-curvature/
conditional/scaling boundary; the review itself is not compilation evidence.

## Next experiment: actual paired scalar jets and global transverse producer

The previous checkpoint is PROGRESS: `71419b7c` supplies checked original
score/budget equalities and is pushed to main. This continuation preserves the
unchanged Clay objective and the original action. Two bounded mathematical
tasks meet at the relative scalar, rather than growing cap-only wrappers.

1. Prove actual paired second scalar jets on blocks 0/1: Ji^2(x)=-x and
   JiJj(x)+JjJi(x)=0 for distinct directions, hence the frozen polynomial
   contraction is -(sum ui^2)*x. Available inputs: the literal relative scalar,
   supported angular carrier differentiation and finite canonical checks.
   Coefficients ui must not be differentiated. Arbitrary-block recoding and
   a geometric heat/PDE identification are separate, not implied by this pin.
2. Construct a GLOBAL one-sided transverse polynomial certificate for the
   literal Jacobi heat h and its ACTUAL formal scalar derivative h_x:

       C_T*h^2-x*h*h_x >= 0,   C_T=2*w/(1-w^2).

   No density-floor reciprocal belongs in C_T. The full interval is covered
   by the exact affine identity, with c=w^(2k+1):

       f-x = ((c^2+2c)*(1+x)+((c-1)^2+1)*(1-x))/2,
       f=1+2*c*x+c^2.

   Retain the Euler factor. Simultaneous positive product/derivative
   induction adds 2*c at each factor; the finite geometric sum is bounded by
   C_T. Use the actual QPoly formal derivative and coefficient identities,
   not merely a recursively defined jet. Initial empty/constant heat cases,
   x=+/-1, full signed x and the normalization are decisive checks.

The second target is an actual partial curvature producer, NOT a global
matrix lower bound: the negative-hemisphere radial mixing inequality remains
unsupplied. The scalar certificate's angular/substitution pin, exact weighted
character join, and transport to the original UNWEIGHTED prefix must be
proved before an original transfer estimate is claimed. Existing absolute
deficits may use the heat floor in their tighter CUT OFF tolerance without
placing its reciprocal in the final curvature cost; the current cutoff alone
does not supply that transport. No global hemisphere assumption is allowed.

Sol implements the bounded leaves; root serializes focused verification,
using one 20-GiB worker, 12-GiB reserve and a fresh dynamic preflight at every
launch. Revise if the actual derivative pin is absent, finite cutoffs or
unit-radius endpoints are dropped, or a full radial/matrix result is inferred
from the transverse leg. No new hypothesis bundle, canonical field change,
routine literature scan or chart reprint is planned.

### Observed scalar-jet and transverse evidence

Both final focused targets PASS. All fourteen printed public dependencies
are exactly {propext, Quot.sound}; no new source sorry/axiom/classical input.

| Declaration | Source |
| --- | --- |
| `pairedScorePlus_zero_derivative_pin` | `lean/YMGap/Continuum/SU2QuaternionPairedFrameScalarJets.lean:54` |
| `pairedDerivative_carrier` | Same source `:90` |
| `relativeScalar_supported` | Same source `:105` |
| `relativeScalar_second_jet` | Same source `:129` |
| `relativeScalar_mixed_jet` | Same source `:139` |
| `frozenScalarSecondJet_pin` | Same source `:212` |
| `frozenScalarSecondJet_weighted_pin` | Same source `:243` |
| `product_formal_derivative_pin` | `lean/YMGap/Continuum/JacobiHeatTransverseCurvature.lean:112` |
| `factor_transverse_certificate` | Same source `:185` |
| `productDerivative_transverse_certificates` | Same source `:234` |
| `transverseCap_denominator_pin` | Same source `:289` |
| `transverseCap_nome_defect_le_one` | Same source `:301` |
| `transversePrefixCost_le_cap` | Same source `:319` |
| `heat_transverse_curvature_certificate` | Same source `:334` |

Accepted logs and SHA-256:

```text
/private/tmp/ym-oct7-paired-scalar-jets-final.log
a1af551a8ae2d384203dd16b7411f9128c2de5af78a6384bf48e7a816f984b5e
/private/tmp/ym-oct7-jacobi-transverse3.log
6dbf688f5c492008d7f0bc43ff312f27415bade37d5ab1e2696318af0ebab4d6
```

The earlier transverse logs are FAILED elaboration, not accepted evidence.
Repairs used named coefficient negation, explicit polynomial/constant
arguments and exact finite-sum normalization; no mathematical hypothesis
changed. Fresh preflights before each launch showed no competing compiler,
87--88% free and zero swap. Verification was serialized with one 20-GiB
worker and 12-GiB reserve. Root import registration only; no full-root/tree
build, full axiom audit or baseline refresh was run.

Independent read-only source review found no material issue: actual second
jets precede multiplication by frozen u, interval certificates retain both
1+x and 1-x, and the formal derivative/Euler/normalization pins are literal.
Its review was not compilation evidence. No geometric group flow, covariant
matrix Hessian, original unweighted heat, OS norm or physical gap is claimed.

Decision: CONTINUE. The transverse coefficient has the desired inverse-linear
nome-defect scale, unlike the prior constructed entrywise cap. The negative-
hemisphere RADIAL mixture is the substantive missing estimate. With
r_k=2*c_k/(1+2*c_k*x+c_k^2), c_k=w^(2*k+1), S_m=sum r_k^m, the still-unproved
denominator-cleared radial target is

```text
C*S1^2 >= (1-x^2)*(S2*S1^2-2*S3*S1+S2^2)
              + x*(S1^3-S1*S2),   C=O(1/(1-w)), N>=N0(w).
```

This is a research target, not a new Lean premise or assertion of an available
cutoff N0. The N=2 diagnostic above prevents claiming it for all finite N.
Scalar substitution/angular heat pins, arbitrary-block recoding, exact
weighted-character derivative transport and the original unweighted cutoff
join must also be established before an original conditional matrix estimate.
Complete signed cost, normalization, independent survival, completed
comparison, physical/volume control, SAME limiting QFT and every-group/Clay
requirements remain OPEN. Supporting proofs change none of the canonical
chart's displayed broad claims; no chart is reprinted.

The current pasted note
`/Users/darthur/.codex/attachments/cf965d8e-085c-42c2-a303-16f0ae70d860/Pasted text.txt`
was read against the existing lattice-mass research audit and work-plan
priority. Its useful numerical-channel versus physical-generator distinction
is already incorporated there, together with finite-spacing and regularity
corrections. No measured mass, transfer/Hamiltonian identification or continuum
regularity hypothesis was imported into these certificates; no duplicate
paper review or routine listing scan was performed.

### Radial experiment selection: retain the product/mixture cancellation

Independent bounded mathematical review supplies a decisive endpoint screen,
checked algebraically by root but NOT yet a Lean theorem. At x=-1 and N>=1,
set r0=2*w/(1-w)^2. Pairing the terms of the finite geometric sum gives

```text
1-w^(2k+1) >= (2k+1)*w^k*(1-w),
r_k(-1) <= r0/(2k+1)^2,
sum_(k=1)^(N-1) 1/(2k+1)^2 <= sum 1/[4k(k+1)] <= 1/4.
```

Thus S1<=5*r0/4 and S2>=r0^2, so S2/S1>=4*r0/5. The COMPLETE radial
endpoint is S1-S2/S1>=0 since S1^2>=S2; however the isolated mixture
contribution is -S2/S1, necessarily of inverse-quadratic nome-defect size.
This persists at arbitrarily large finite cutoffs. Separately imposing
inverse-linear floors on product and mixture therefore cannot prove the
desired joined bound. PRUNE that split, NOT the full radial/onset target,
the original action, or Yang--Mills. The next producer must retain their
cancellation (and the radial positive-mixture variance); no premise or
canonical frontier field changes. This screen is mathematical research
evidence, kept distinct from the fourteen kernel-checked gates above.

## Next bounded experiment: contract radial mixture to product curvature

Root verified the exact scalar cancellation, but no Lean result is yet claimed
in this section. Put a=1-x^2, D=a*S2+x*S1, with S_j the finite r-power sums.
The cleared radial numerator is exactly

```text
Lnum = -(S1^2-S2)*D + 2*a*(S1*S3-S2^2).
C*S1^2+Lnum = (C-D)*(S1^2-S2)+C*S2+2*a*(S1*S3-S2^2).
```

Available constructive finite inputs: r_i>=0, so S1^2-S2>=0 and
S1*S3-S2^2>=0, the latter by weighted squared pair differences. Thus a>=0,
C>=0 and the PRODUCT bound D<=C suffice. No reciprocal S1 or heat floor is
needed, and the empty prefix is included. The direct consumer is the radial
research target above; this is a strictly sharper mathematical reduction,
not an assumed original gap or new frontier bundle.

Sol implements the finite rational identities/positivity; root alone runs the
focused 20-GiB check after a fresh preflight. An independent read-only review
locates the exact remaining same-product Gaussian/second-derivative input.
Predicted outcome: finite cancellation contracts; the Poisson/curvature input
remains open. Revise if any moment is not the actual finite prefix, positivity
is silently assumed instead of proved, a division excludes zero prefixes, or
a Poisson equality/physical time is inferred from the algebra. Auxiliary
circle time t_theta=-log(w) must not be identified with the carrier time
-4*log(w) or standard g^2=-8*log(w). No geometric or continuum closure.

### Narrow analytic route, without importing a classical premise

The underlying P(w,cos(theta)) is the theta3 product at angle theta/2, not
the SU(2) derivative heat itself. The product normalization and modular
transformation are classical benchmarks in
[NIST DLMF 20.5.3](https://dlmf.nist.gov/20.5.E3) and
[20.7.32](https://dlmf.nist.gov/20.7.E32). Root's inference from those formulas:
for auxiliary circle time t_theta=-log(w), P is proportional to the positive
wrapped Gaussian sum G=sum_j exp(-(theta-2*pi*j)^2/(4*t_theta)). Its cleared
log-Hessian is -G^2/(2*t_theta) plus a nonnegative weighted variance. This
suggests D_infinity<=1/(2*t_theta), NOT an imported constructive theorem.

For a cutoff with w^(2*N+1)<=1/8, the negative product tail costs at most
sum_(k>=N) r_k<=8*w^(2*N+1)/(1-w^2)<=1/(1-w). Together with
t_theta>=1-w this suggests C=3/[2*(1-w)] for the finite joined radial
expression. These are research estimates pending actual derivative, tail
and limit proofs, not an available physical bound or established Lean cutoff.

The needed analytic join is specifically the SAME theta3 PRODUCT's Gaussian
identity and first/second angular derivative control with explicit moduli.
Do not unnecessarily demand a full SU(2)/Faraut image formula or its sine-
denominator endpoint removal: h is reached through finite algebra instead.
Existing `JacobiTripleProductOnBox.thetaProduct_eq_fullThetaSeries`
(`lean/YMGap/Continuum/JacobiTripleProductOnBox.lean:91`) already identifies
the all-nome on-box product with the normalized cosine series. It does not
prove the Poisson/Gaussian or second-derivative join. `JacobiModularCReal`
explicitly withholds modular inversion, and the Faraut image formulas remain
supplied inputs. No classical source is added as a Lean axiom or hypothesis;
angle/carrier, finite-to-limit and physical-time identifications stay OPEN.

### Observed finite radial cancellation evidence

The final focused target PASSes all seven gates within {propext, Quot.sound}.
The first three moment nonnegativity theorems use propext only.

| Declaration | Source |
| --- | --- |
| `M1_nonneg` | `lean/YMGap/Continuum/JacobiHeatRadialMixtureCancellation.lean:50` |
| `M2_nonneg` | Same source `:54` |
| `M3_nonneg` | Same source `:57` |
| `first_square_gap_nonneg` | Same source `:63` |
| `moment_variance_nonneg` | Same source `:112` |
| `radialNumerator_cancellation` | Same source `:157` |
| `radialMixture_payment_nonneg` | Same source `:177` |

Accepted log and SHA-256:

```text
/private/tmp/ym-oct7-radial-mixture2.log
0abeaf288548027f0a0b4267a1c4bde6a26a75dfa1be4382f716ca65c07d7f0d
```

Initial elaboration failed on a missing convenience congruence, unreduced
empty-prefix goals and a function-pattern layout. Root used the core rational
congruences and explicit empty reduction; no hypotheses changed. No source
sorry/axiom/classical input. Both preflights showed no competing compiler,
87--88% free and zero swap; one 20-GiB worker, 12-GiB reserve. No full-root/tree
build/audit or baseline refresh. This is finite rational algebra, not yet an
actual angular heat inequality.

Independent read-only review confirmed the actual moment sums, constructed
variance/pair positivity, empty case and full signed numerator/payment. It
also confirmed the narrower missing theta3 circle-Gaussian bridge: no full
SU(2) Faraut sine-denominator formula is needed for this route. The review
itself is not compilation evidence.

Decision: CONTINUE from the PROVED finite reduction to a genuine product
curvature producer and SAME heat-jet/cutoff/conditional joins. No separated
mixture floor, global density-floor cost, or classical Poisson premise is
introduced. The finite derivative/moment identifications, Gaussian derivative
limits, useful original signed cost, scaling, independent survival, completed
comparison and all physical/continuum/Clay obligations remain OPEN. Together
this continuation checks three focused leaves and twenty-one public gates,
without changing any canonical displayed broad claim. No chart reprint.

## Next experiment: actual radial heat/moment jet join

Previous checkpoint `75075d27` is verified PROGRESS and pushed to main.
The finite radial algebra must now refer to actual Jacobi derivatives before
it is a heat estimate. For r_i=HKConv.sTerm(w,x,i), retain the same full
Euler-weighted product P and normalized heat h=(inverseNome/2)*P'_x.
Prove the actual FORMAL first three product jets at 1+x:

```text
P'   = P*S1,
P''  = P*(S1^2-S2),
P''' = P*(S1^3-3*S1*S2+2*S3).
C*h^2+(1-x^2)*(h*h_xx-h_x^2)-x*h*h_x
     = (inverseNome*half*P)^2*(C*S1^2+Lnum).
```

Consumer: `JacobiHeatRadialMixtureCancellation.radialMixture_payment_nonneg`.
Inputs already available are the literal shifted product/heat, formal
Leibniz rules, first-derivative normalization and factor/sTerm cancellation.
The output is an ACTUAL finite scalar heat implication given the smaller
PRODUCT ceiling; it does not produce that analytic ceiling. Empty/constant
prefixes, x=-1, full signed x and the normalization are decisive tests.
No derivative is freely supplied in lieu of formal differentiation.

Sol implements the bounded actual-jet leaf, root checks it with one 20-GiB
worker and 12-GiB reserve after a fresh dynamic preflight. A parallel math
review seeks a shorter signed product ceiling without insisting on a full
Poisson formalization; another reviews the later Haar-certificate join.
Revise if only recursive free jets are pinned, any factor/normalization is
dropped, a zero case is excluded, or pointwise order is silently treated as
Haar-square/conditional/OS order. No new frontier bundle or field weakening.

The eventual polynomial certificate route may use the cleared identity
`P*Lheat=P''*Qproduct+C*P*(P'^2-P*P'')+2*(1-x^2)*P^3*variance`.
Its positivity and positive-multiplier removal must themselves be constructed
under arbitrary original action insertions; this paragraph is a research
target, not that missing proof. No chart claim changes from selecting it.

### Observed outcome: ACTUAL finite heat-jet join checked

The experiment succeeds at its stated scalar scope. All nine load-bearing
declarations in `JacobiHeatRadialMomentJets.lean` pass the focused check and
print exactly {propext, Quot.sound}. No elaboration retry or statement change
was needed. The public padded-coefficient evaluation bridge is reused.

| Declaration | Source |
| --- | --- |
| `product_derivative_coeff_pin` | `lean/YMGap/Continuum/JacobiHeatRadialMomentJets.lean:130` |
| `product_first_moment_pin` | Same source `:142` |
| `product_second_moment_pin` | Same source `:149` |
| `product_third_moment_pin` | Same source `:175` |
| `heat_eval_moment_pin` | Same source `:214` |
| `heat_first_moment_pin` | Same source `:226` |
| `heat_second_moment_pin` | Same source `:242` |
| `heat_radial_moment_pin` | Same source `:265` |
| `heat_radial_nonnegative_of_productCost` | Same source `:305` |

Accepted log and SHA-256:

```text
/private/tmp/ym-oct7-radial-moment-jets1.log
ba78f37d8dd70c8a081efe89bd38818a1382990b06a7cc3a160bb334fa333a9b
```

Root read the complete source; independent read-only review confirmed actual
formal pderiv through order three, literal sTerm/factor cancellation, repeated
index terms, inverseNome*half normalization, and empty/constant prefixes.
The final expression consumes exactly C>=0, x^2<=1 and actual D<=C. No heat
or moment density is inverted. This closes the scalar heat/moment pin missing
from checkpoint 75075d27; it does NOT produce the product ceiling.

Fresh escalated preflight found no competing compiler, 88% free and zero
swap. One capped 20-GiB worker, 12-GiB reserve; no full-root/tree build/audit
or baseline refresh. The root import is registered, not a full-root check.
No new sorry/axiom/classical input or canonical frontier change. Broad chart
unchanged; no reprint.

### Parallel product-ceiling and certificate review

These are mathematical/source reviews, not new Lean evidence. For the
negative hemisphere the elementary signed summand
F(s)=(1+x*cosh(s))/(cosh(s)+x)^2 has integral one. For -1<x<0 it has a
single negative minimum and total variation at most 3/[2*(1+x)]. Midpoint
quadrature would bound the infinite sum by 1/(2*t_theta)+3/[4*(1+x)],
giving an inverse-linear nome-defect ceiling when 1+x>=1-w. At
x<=-2*w/(1+w^2), every finite summand is nonpositive. This leaves the strip
`(1-w)^2/(1+w^2) < 1+x < 1-w`; its width is not a payment under the
original action. No global elementary summed bound was found.

A fixed-multiplier termwise telescoping shortcut fails: at w=1/2,c=1/8,
the comparison using g(c)=(1-c^2)/(1+2*c*x+c^2) would require K>=85/81
at x=1 and K<=45/49 at x=-1. This rejects that particular comparison,
not the summed target or Yang--Mills. Retain signed corrections or use the
genuine theta3 Gaussian bridge.

The prospective cleared polynomial identity and pair-variance exponent 3
were independently confirmed. Existing square-certificate multiplication,
positive-coefficient substitution and positive-window order reflection can
retain overlapping variables and a certified original action weight. The
missing analytic producer is a SAME finite Certificate for
`Qproduct=C*P^2-(1-x^2)*(P'^2-P*P'')-x*P*P'` with useful nome dependence.
Scalar pointwise positivity is not such a certificate. Positive-multiplier
reflection cancels only in a Haar expectation; it does not assert polynomial
certificate division. An actual action weight must also be certified before
it is used in that construction.

Decision: CONTINUE from the checked actual heat-jet reduction to that genuine
product-ceiling producer and its Haar/conditional join. Do not extend wrappers
that re-assume it, split away the mixture variance, or identify the auxiliary
circle clock with physical time. Explicit angular/cutoff/limit transport,
useful original signed cost, scaling, independent survival, completed
comparison and all physical/continuum/Clay obligations remain OPEN.

## Next experiment: theta addition square and signed finite cutoff

Checkpoint a71313a4 is verified PROGRESS and pushed to main. The next
producer remains the useful SAME-product radial ceiling, not another
consumer that assumes it. Root found a shorter algebraic candidate than
Poisson/modular inversion; two independent mathematical screens confirm
the sign and constants. This section is a DERIVATION/PLAN, not Lean evidence.

### The addition square, without a Gaussian or physical-clock premise

Use [DLMF 20.7.8](https://dlmf.nist.gov/20.7.E8), together with
[20.7.2](https://dlmf.nist.gov/20.7.E2) and
[20.7.4](https://dlmf.nist.gov/20.7.E4). Multiplying E8 by theta3(0)^2,
substituting E2 for theta4(z)^2, and substituting E4 for the remaining
theta2/theta3 difference gives, after positive theta4(0)^2 cancellation,

```text
g0^2*g(z+u)*g(z-u) = g(z)^2*g(u)^2 + theta1(z)^2*theta1(u)^2,
g(z)=theta3(z,w), g0=g(0).
```

E8 is not verbatim this identity; the conversion is essential. An alternate
pure-convolution derivation uses [Watson E13/E14](https://dlmf.nist.gov/20.7.E14)
and the elementary dot-product/determinant square identity. Splitting a
bilateral double sum by equal parity under (m,n)->(m+n,m-n) is the proposed
constructive proof; reindex the finite domain and bound its boundary before
passing to the limit. Literal same-N truncated theta sums do NOT satisfy
the infinite addition identity exactly.

Twice differentiating in u at zero gives

```text
g0^2*(g*gzz-gz^2) - g0*gzz(0)*g^2 = theta1'(0)^2*theta1(z)^2 >= 0.
```

For x=cos(2z), the angular logarithmic curvature is -4*D_infinity(x).
Hence the derived ceiling is

```text
D_infinity(x) <= D_infinity(1)
              = sum_i 2*c_i/(1+c_i)^2
              <= C_T = 2*w/(1-w^2) <= 1/(1-w).
```

No limiting curvature, addition identity or differentiated equality is
currently a produced Lean input. Existing product/cos-series equality alone
does not supply them. The auxiliary argument is not physical time.

Fractional powers, sine coordinates and elliptic functions need not be
introduced into the rational cleared target. Put

```text
R_n(x) = 1 + 2*sum_{k=1}^n T_k(x),
A(x) = sum_{n>=0} (-1)^n*w^(n*(n+1))*R_n(x),
B    = sum_{n>=0} (-1)^n*(2*n+1)*w^(n*(n+1)).
P0^2*[D0*P^2-(1-x^2)*(P'^2-P*P'')-x*P*P']
      = 2*w*(1-x)*A(x)^2*B^2,
P0=P(1), D0=P'(1)/P0.
```

This is the same square after eliminating theta1's quarter-nome and
half-angle factors; its sign and factor two were independently checked.
For the FULL Euler-weighted product, P=1+2*w*x+O(w^4); no spurious w^2
term is retained. Needed new proof: actual convergent parity convolution,
the appropriate formal derivative/limit pins and explicit tail moduli.

### The independent finite tail producer

For the ACTUAL rational factor r_i=2*c_i/(1+2*c_i*x+c_i^2), retain
d_i=(1-x^2)*r_i^2+x*r_i. On [-1,1], the proposed exact cleared identity
`factor_i^2*(r_i-d_i)=2*c_i*(1-x)*(1-c_i)^2` proves d_i<=r_i;
d_i+r_i>=0 proves the other sign. At c_N<=1/8, each tail denominator
is at least 1/2, so r_{N+j}<=4*c_N*(w^2)^j and an explicit sufficient
finite-to-finite error is E_N=4*c_N/(1-w^2), with
`(1-w)*E_N<=1/2`. Combined with the ADDITION ceiling, this would give
`D_N<=3/[2*(1-w)]`. This does not assume finite-product monotonicity.

Sol implements that bounded actual signed-tail leaf; root alone compiles
with one 20-GiB worker and 12-GiB reserve after a fresh dynamic preflight.
Its immediate consumer is finite cutoff transport of the addition-square
ceiling to the actual jets in JacobiHeatRadialMomentJets. Revise if the
sign of omitted terms is lost, positivity of the denominator is assumed
without proof, the cost includes an original heat-floor reciprocal, or an
infinite identity is claimed for literal finite truncations.

### The strict scalar-to-Haar join already has an actual consumer

Root read `QuaternionHaarBernsteinRowCertificate.strictPolynomialCertificate`
(`lean/YMGap/Continuum/QuaternionHaarBernsteinRowCertificate.lean:205`): an
explicit STRICT rational interval margin computes a Bernstein cutoff/row
and an exact original Haar square certificate, with no loss in the target
polynomial. `QuaternionHaarUnitIntervalCoordinate.unitArgument_certificate`
and `oneMinusUnitArgument_certificate` supply its actual coordinates from
a constructed unit square bound.

After the missing addition ceiling and checked tail, choosing
C=2/(1-w) leaves slack delta=1/[2*(1-w)]. The finite product's explicit
positive lower bound ell_N=product_i Euler_i*(1-c_i)^2 would give
`Qproduct >= ell_N^2*delta`. That margin, not a mere non-strict sign,
is the required input to the EXISTING Bernstein producer. A small ell_N
may enlarge its approximation modulus; its reciprocal is NOT placed in
the curvature coefficient. Then retain any certified overlapping original
action by certificate multiplication and use the existing positive-window
Haar order reflection for positive multipliers. This join still needs the
actual interval margin, product lower bound and original-action instantiation.

Decision: REVISE analytic selection toward the shorter addition-square
producer; retain Poisson as an alternative, not an extra required obstacle.
No new bundle, weakened canonical field, classical premise, chart closure
or physical mass claim follows from this research selection.

## Observed proof increment: actual signed radial limit and cutoff transport

The finite-tail experiment succeeded. Root read both full new sources;
independent Sol mathematical review found no material sign, constant or
scope defect. This section records kernel evidence, separately from the
addition-square research above.

- `lean/YMGap/Continuum/JacobiProductRadialSignedTail.lean:60`,
  `radialSummand_sum_pin`, pins the literal signed sum to the actual
  `productRadialCost`. At line 72, `radialSummand_bounds` proves
  -r_i<=d_i<=r_i on the FULL interval. Its exact cancellation is
  f_i-(1+x)*2*c_i=(1-c_i)^2; no sign of d_i is discarded.
- At line 148, `sTerm_tail_le_four_geoAmp` uses c_N<=1/8, hence each omitted
  denominator >=1/2, to prove r_(N+j)<=4*c_(N+j). At line 178,
  `sTerm_finite_tail_le` sums this against the actual geometric tail.
  At line 215,
  `productRadialCost_finite_tail_le` gives D_N<=D_(N+L)+E_N for every L.
- `radialTailPayment_denominator_pin` (line 238) and
  `radialTailPayment_nome_defect_le_half` (line 252) pin E_N*(1-w^2)=4*c_N and
  (1-w)*E_N<=1/2. The onset remains an explicit hypothesis; these theorems
  do not silently produce a cutoff or the infinite ceiling.
- `lean/YMGap/Continuum/JacobiProductRadialLimit.lean:131`,
  `productRadialCostCReal`, constructs the actual D_N sequence. At line 143,
  `productRadialCostCReal_approx` is rfl. `radialTolerance` (line 86) and
  `radialCutoff` (line 90) are Q'/Nat data; `radialCutoff_tail_le` (line 108)
  and `radialCutoff_cauchy` (line 168) prove the explicit convergence
  modulus, uniform in x at each named w. The legacy Prop modulus is filled
  from named data, never used to extract that data.
- `productRadialCost_le_limit_ceiling` (line 191) consumes a bound on THIS
  limit and transports it to D_N<=C+E_N using the signed finite comparison
  at max(N,M), then removes the rational precision error. Cstar(w) occurs
  only in convergence, not the finite ceiling coefficient.

### Exact verification boundary

One worker, mandatory 20-GiB ceiling, 12-GiB reserve. Fresh dynamic
preflights before each launch found 87--88% free memory, zero swap and no
competing Lean/Lake/pytest/runner processes. Root used only the monitored
launcher. The first signed-tail check failed on 0+j normalization, not
mathematics; an explicit Nat.zero_add rewrite repaired it without changing
any statement. Failed-check sorryAx output is NOT proof evidence.

Final focused checks, each emitting an olean:

```text
/private/tmp/ym-oct7-radial-signed-tail2.log
SHA256 ca3fd8e53c0b1ea6c2a4135851b321b387dfe5c2d6f7ad288700ac269305b3dd
7 printed gates pass, all within {propext, Quot.sound}.

/private/tmp/ym-oct7-radial-limit1.log
SHA256 3a61c927d2b771e3eb36f65770118dbd9cd4527b7a8bee60a2d6670bc289029c
10 printed gates pass, all within {propext, Quot.sound}.
radialTailPrefactor, radialTolerance and radialCutoff are axiom-free.
```

No full-root/tree build or audit, baseline refresh, new source sorry/axiom,
classical input or canonical field change. Root imports are registered;
this is not a full-root check. The canonical displayed claims remain open,
so the ASCII chart is unchanged and not reprinted.

### Continue: actual convolution, not another assumed-ceiling consumer

The addition/derivative-limit ceiling is the missing producer. Independent
research review spells out the finite geometry: (m,n)->(m+n,m-n) has an
even class m=j+k,n=j-k and odd class m=j+k+1,n=j-k. The exponent pins are
2*j^2+2*k^2 and 2*j*(j+1)+2*k*(k+1)+1. The original |m|,|n|<=N box becomes
the even |j|+|k|<=N diamond or the odd half-shifted diamond, NOT the whole
containing rectangle. For either class, omitted shells T>=N+1 have at most
4*T points, exponent >=T^2 and second-angular weight <=4*T^2; proposed
error is bounded by 16*sum_(T>=N+1) T^3*w^(T^2). These statements are
RESEARCH until the exact finite reindex/tail producer is checked.

Root also read the whole existing `ThetaProductStrictFloor.lean`:
`floor_le_Ppart` (line 91) supplies a positive floor for the ACTUAL
Euler-weighted finite product, uniform in x,N at each named nome;
`thetaConvCRealGen_geRat_floor` (line 101) covers its existing completion.
Thus a new floor module is unnecessary. With a genuinely produced ceiling
and strict slack delta, Qproduct>=delta*floor(w)^2 would feed the EXISTING
Bernstein producer. This affects the certificate modulus, not the curvature
constant. No strict margin/Haar/action certificate is claimed here.

Decision: CONTINUE the shorter addition-square producer with bounded finite
reindex work and independent mathematical review. Retain derivative-limit,
original weighted conditional/scaling and all downstream Clay obligations.

## Observed proof increment: finite addition-route producers

The next bounded experiments also supply actual objects/estimates rather
than another assumed-addition consumer. Root inspected complete sources;
independent Sol reviews checked signs, zero/negative indices, normalizations
and the exact remaining scope.

- `lean/YMGap/Continuum/ThetaParityConvolution.lean:314`,
  `signed_box_parity_convolution`, proves the full arbitrary-weight finite
  signed-box equality to EVEN+ODD DIAMOND sums. `encode_decode` (line 46),
  `decode_encode` (line 68) and `boxParityDecode` (line 212) carry explicit
  inverse/boxed data. `even_frequency_pin` / `odd_frequency_pin` (73/79)
  and `even_exponent_pin` / `odd_exponent_pin` (85/93) retain both branches,
  including the odd exponent +1. The containing box N+1 is only an
  enumeration device; `evenDiamondIndices_mem` / `oddDiamondIndices_mem`
  (179/195) impose EXACT transformed original-box constraints. N=0 has one
  even cell and no odd cells. No rectangle substitution is claimed.
- `lean/YMGap/Continuum/ChebyshevHalfShiftProduct.lean:113`,
  `halfShift_product`, constructs the exact shifted kernel
  (1-x)*C_n*C_m=T_dist-T_(n+m+1), C_n=U_n+sinCoord n. `rotation_difference`
  (line 86) is proved from existing rotation addition and Pythagorean
  identities, on both index orders. Arbitrary rational x and zero indices
  are included; n=m=0 gives 1-x. This supplies finite algebra for the
  independent shifted/alternating convolution, not that completed identity.
- `lean/YMGap/Continuum/JacobiProductRadialEndpoint.lean:31`,
  `productRadialCost_at_one_pin`, gives the ACTUAL D_N(1)=M1. At line 40,
  `endpoint_sTerm_le_rate` uses the actual denominator 1+2*c+c^2>=1.
  `productRadialCost_at_one_le_cap` (54) and
  `productRadialCostCReal_at_one_le_cap` (65) therefore produce the useful
  endpoint ceiling C_T=2*w/(1-w^2), on every prefix and the SAME constructed
  limit. The whole-interval comparison D_infinity(x)<=D_infinity(1) is NOT
  supplied. No heat-floor reciprocal enters this ceiling.
- `lean/YMGap/Continuum/ThetaAngularShellTail.lean:87`,
  `shellTerm_succ_le_half`, proves the actual shell 16*T^3*w^(T^2)
  contracts by half after `shellOnset` (line 34). The constructive onset
  max(1,powBaseCutoff(w,1/16)) forces w^(2*T+1)<=1/16, and cubic growth
  costs at most 8. `shellTail_le_two` (line 135) bounds every finite tail
  by twice its first shell. `shellTolerance` (161), `shellTailCutoff` (165)
  and `shellTail_le_epsilon` (192) retain explicit rational/Nat data paying
  epsilon at every later index. The angular shell count and domination
  of actual convolution errors are still missing joins, not hypotheses
  silently discharged by this scalar leaf.

### Exact verification boundary

Same monitored one-worker policy and fresh dynamic preflight at EACH launch:
87--88% free memory, zero swap, no competing compiler/test/runner process;
mandatory 20-GiB worker ceiling and 12-GiB reserve. Final focused evidence:

```text
/private/tmp/ym-oct7-theta-parity2.log
SHA256 95021dc5c73842ad76f11b33363e4cd54771127527bde5de47e18543666a796e
13 public printed gates pass in {propext, Quot.sound}.

/private/tmp/ym-oct7-radial-endpoint1.log
SHA256 d1701accb555e21641cc8b4d92d4e05159fb1b931476cf292e9edb4934007f75
4 public printed gates pass in {propext, Quot.sound}.

/private/tmp/ym-oct7-halfshift1.log
SHA256 e19bbddd4f8e8c3e8a5d7ddcb08f8439184f367d2460780bbeb39d3740e21627
5 public printed gates pass; natDist and halfShiftCoord are axiom-free.

/private/tmp/ym-oct7-angular-shell4.log
SHA256 3f78f9bb909c75c73626d150f425e801021960e2f7919291a231709d360c9f69
8 public printed gates pass; shellTerm, shellOnset, shellTolerance and
shellTailCutoff are axiom-free.
```

The first parity check failed map-lambda typing, diamond decidability and
hidden-definition transport; the statements were unchanged in repair.
Static review removed a false UNUSED arithmetic equality before any shell
compile. Initial shell checks failed imports, unsupported tactic, lambda/
parenthesis parsing and explicit-argument normalization; the final source
passes. Failed-check sorryAx output is not evidence. No source sorry/axiom,
classical input, canonical field change, baseline refresh or full-root/tree
check/audit. Imports are registered without claiming full-root verification.
The displayed canonical goal claims remain open, so there is no chart reprint.

### Narrower mathematical join selected (RESEARCH, not a proved identity)

Use normalized half-nome series without square roots:

```text
E(x)=1+2*sum_(n>=1) w^(2*n*n)*T_(2*n)(x),
H(x)=sum_(n>=0) w^(2*n*(n+1))*T_(2*n+1)(x),
P(x)^2=E(1)*E(x)+4*w*H(1)*H(x),
K(x)=E(1)*H(x)-H(1)*E(x).
```

The coefficient is 4*w, not 2*w. After the still-missing actual convergent
convolutions, the elementary determinant square yields

```text
P(1)^2*(E(x)*E(y)+4*w*H(x)*H(y))-P(x)^2*P(y)^2
  =4*w*K(x)*K(y).
K(x)=(x-1)*A(x)^2, K'(1)=B^2, B=A(1).
```

Only the endpoint first scalar jet in y is needed. Its actual finite joint
kernel is the signed-box weight
w^(m^2+n^2)*T_|m+n|(x)*T_|m-n|(y). The endpoint derivative has weight
(m-n)^2; completing that convolution would give
E(x)*E'(1)+4*w*H(x)*H'(1)=2*D_infinity(x)*P(x)^2.
The differentiated determinant then gives the originally proposed square
2*w*(1-x)*A(x)^2*B^2. Independent mathematical reviews confirm these signs
and factors. Neither of the completed equalities is a Lean input yet.

Available first-derivative bridge inspected by root in full:
`lean/YMGap/Continuum/FiniteJacobiDerivativeComparison.lean:252`,
`fullProdDx_sub_two_dPartial_close`, already supplies the actual finite
Jacobi FIRST-jet comparison with explicit cutoff. Reuse it. It does not
supply the combined second-jet deficit required by D. Existing
`lean/YMGap/Continuum/ChebUDClosure.lean:389`, `udClosure`, supplies the
scalar Chebyshev angular ODE; the finite second formal-jet pin and weighted
coefficient comparison remain necessary. No general angular calculus or
Poisson/modular detour is imposed.

Decision: CONTINUE by specializing the checked finite reindex to actual
theta/jet weights, proving diamond-to-rectangle shell domination, and
composing SAME series limits. Then prove the shifted/alternating square and
the actual combined jet comparison. The endpoint ceiling and signed finite
tail are now produced, so the residue is smaller. Do not replace the missing
join by a theta-addition premise, identify each finite truncation with the
limit, or infer a Haar/conditional/physical gap from these scalar lemmas.

## Next bounded experiment: actual combined angular Jacobi comparison

Exact proposition: the literal Euler-weighted polynomial's angular jet
`(1-x*x)*P''-x*P'` approaches the corresponding bare theta angular sum,
with a computed cutoff uniform in x on [-1,1] at each named nome. This
removes the combined second-jet comparison input from the addition-route
radial ceiling; it does not itself prove the addition identity or ceiling.

Available inputs: `FiniteJacobiIdentity.Ppart_eq_finiteJacobi` is an
all-rational finite equality; `ChebyshevFormalJets` pins both ACTUAL formal
jets and `(1-x*x)*T_n''-x*T_n'=-n*n*T_n`. Constructive coefficient reflection
can lift the all-point finite equality before differentiation. Unit-slope
affine translation is still needed to identify the already-used shifted
product jets. The actual coefficient deficit is controlled by
`FiniteJacobiSeriesComparison.coefficientError_succ_le_gaussian`; the
existing `FiniteJacobiDerivativeComparison.shiftedGaussian_le` absorbs
the same quadratic frequency factor, without estimating T_n'' separately.

Prediction/test: the whole angular error has the existing explicit
`derivativeScale(w)*w^(2*N+1)` budget. Constant/empty order must give zero;
both endpoints must be included; nome dependence must stay explicit.
Verification: source review and serialized focused capped targets only,
no new general angular calculus or full-tree audit. Revise if the jet join
requires a substituted polynomial or an assumed second-derivative pin.

## Observed proof increment: actual angular comparison and finite endpoint jets

The selected combined second-jet comparison is now produced, not a supplied
premise. Completed additions, ceilings and physical joins remain open.

- `lean/YMGap/Continuum/ChebyshevFormalJets.lean:39`, `Tpoly`, is the actual
  first-kind coefficient recurrence. `eval_Tpoly_derivative` (130),
  `eval_Tpoly_second_derivative` (187) and `first_derivative_at_one` (199)
  pin both actual formal jets and T'_n(1)=n^2, including degree zero.
  `coefficients_of_eval_eqv` (163) constructively reflects all-rational
  evaluation equality into padded coefficients; `formal_angular_ode` (245)
  states the actual `(1-x*x)*T_n''-x*T_n'=-n^2*T_n` for every rational x.
- `lean/YMGap/Continuum/QPolyAffineJetTranslation.lean:31`, `translate`,
  reuses actual Horner composition with [c,1]. `eval_translate_derivative`
  (105), `derivative_coeff_pin` (122), `second_derivative_coeff_pin` (128)
  and `eval_translate_second_derivative` (133) derive both unit-slope jets.
  The existing shifted Jacobi product is retained, not replaced by a free
  derivative sequence or assumed chain rule.
- `lean/YMGap/Continuum/FiniteJacobiAngularComparison.lean:143`,
  `product_series_coeff_pin`, reflects the ACTUAL Euler-normalized finite
  identity before differentiation. `productAngularJet_pin` (154) gives the
  exact whole angular series with -n^2 coefficients. The actual signed
  coefficient deficit is retained by `productAngularJet_sub_bare_pin` (188).
  `productAngularJet_sub_bare_le` (245) pays its whole error by the existing
  explicit `derivativeScale(w)*w^(2*N+1)`; `productAngularJet_sub_bare_close`
  (269) uses the existing Q'/Nat cutoff, uniform x on [-1,1] at named w.
  The quadratic Gaussian majorant suffices because the jets are combined,
  not separately estimated by fourth-degree frequency weights.
  `productRadialNumerator_pin` (288) proves
  `(1-x*x)*(P')^2-P*((1-x*x)*P''-x*P')=P^2*D`
  for the SAME literal product and HKConv.sTerm moments, without division.
- `lean/YMGap/Continuum/ThetaParityWeights.lean:119`, `thetaCell_even_pin`,
  and `thetaCell_odd_pin` (137) factor the actual cells, with exactly one
  odd w and natural exponents valid on negative indices. `theta_box_eq_diamonds`
  (202) and `frequency_box_eq_diamonds` (218) specialize the actual finite
  reindex. `thetaCellPolynomial_endpoint_derivative` (246) and
  `thetaSumPolynomial_endpoint_derivative` (282) now pin frequency weights
  to ACTUAL finite coefficient derivatives, including zero/empty cases.
  This is a scalar y-jet at y=1; no infinite/angle derivative is asserted.
- `lean/YMGap/Continuum/ThetaParityShellGeometry.lean:33`,
  `evenDiamond_iff_radius`, and `oddDiamond_iff_radius` (176) give exact
  domain geometry. `even_exponent_ge_radius_sq` (150) and
  `odd_exponent_ge_radius_sq` (339) give BOTH Gaussian exponent bounds;
  `even_frequencies_le_radius` (156) and `odd_frequencies_le_radius` (169)
  give the two caps. `oddRadius_eq_encoded_corner_max` (301) and actual
  encoded exponent pinning make the odd estimate a direct max-square bound.
  No shell count or actual weighted-sum domination is supplied yet.

### Exact verification boundary

All five final focused targets pass. Public printed gates stay within
{propext, Quot.sound}; computational definitions with gates are axiom-free.
No new sorry/axiom/classical premise, native_decide, field weakening, baseline
refresh or full-root/tree audit. Root imports are registered, not root-built.
Every launch used one 20-GiB worker, a 12-GiB reserve and a fresh process/
memory preflight; free memory stayed 85--88% and swap zero. No limits raised.

```text
/private/tmp/ym-oct7-chebyshev-formal-jets2.log
SHA256 b88bdde01eced69d595d6b58ae06979b431127d665e41a89ae10eb4150aba0c9
10 public printed gates; Tpoly and H are axiom-free.

/private/tmp/ym-oct7-affine-jet-translation1.log
SHA256 ff61d90241514337ea4ae32beeef96f636e72eb9b961c0df308a749e21c8887e
6 public printed gates; translate is axiom-free.

/private/tmp/ym-oct7-jacobi-angular-comparison3.log
SHA256 e5ecb234c27e180c06af1aa1a36dc25814b8ba2cc61e6230e210e0c20ee8b88e
13 public printed gates; five definitions are axiom-free.

/private/tmp/ym-oct7-theta-parity-weights3.log
SHA256 ec6afae30c81ea700993079e6682688e16dfac16181c716fba831bff719e836b
15 public printed gates; both cell/sum polynomial definitions are axiom-free.

/private/tmp/ym-oct7-parity-shell-geometry6.log
SHA256 f6406c6a9f2a49a75729aac9daa263338d0a5c59e28a7be48ffc0a32908d3628
8 public printed gates; all permitted.
```

Root inspected the complete final sources. Independent read-only mathematical
reviews found no substantive defect in actual jets, coefficient reflection,
angular signs, Gaussian budget, radial cancellation, parity weights and all
domain sign quadrants. Initial elaboration failures (casts, match layout,
recursion unfolding and a misplaced proof block) are not proof evidence.
The geometry initially elaborated with Classical.choice through omega on
conjunction goals; explicit conjunction introduction removed that dependency
in the final checked source. No such intermediate version is committed.

### Decision and smaller residue

CONTINUE: count the actual shells and pay omitted weighted sums, then compose
the actual diamond/rectangle series limits and shifted/alternating square.
The finite angular comparison and endpoint formal-jet producers are now
available. The raw Gaussian box's SAME-N endpoint jet belongs to bare F_N,
NOT finite Euler-weighted P_N: their completed identification still needs
the proved comparison and convergence joins. Never assert a per-N equality
between that box jet and `2*productRadialNumerator`.

Completed addition/whole-interval ceiling, strict Haar/weighted conditional
join, scaling/signed-cost estimates, independent survival, completed OS
comparison, physical/volume control, SAME limiting QFT, every group and Clay
remain OPEN. The displayed canonical claims have not changed, so no chart
reprint is warranted.

## Exact bare-Haar family/long-loop obstruction (2026-10-08 UTC)

The bounded MAIN screen recorded in `work_plan.md` now has kernel evidence.
`lean/YMGap/Continuum/BF4DyadicWilsonSquareHeatImage.lean:187`,
`paddedSquare_fundamental_family_haar_zero`, proves

    H[spatialSpan(width,c,qs) * fundamental(paddedSquare(scale,width))] = 0

as rational equivalence, assuming only strict physical padding,
`1 < side scale`, and membership of every literal family face in
`spatialFaces width`. Arbitrary signs, repeated faces, empty families and
zero coefficients are allowed. The side-one equal-eigenvalue case is
deliberately excluded. No interacting measure appears in this statement.

The proof uses the ACTUAL eigenimages
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`,
`spatialSpan_fullRange`, and the existing square theorem in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareHeatImage.lean:108`,
`paddedSquare_fundamental_fullRange`. Symmetry is
`lean/YMGap/Continuum/SU2QuaternionProductHeatDualForm.lean:44`,
`kineticPair_symm`. Each API is algebraic for arbitrary rational reference
nome. Choosing reference w=2,K=1 yields

    [2^(12*side scale)-2^12] * H[f*F] = 0.

Exact numerator/denominator induction and strict natural-power comparison
make the bracket positive. The constructive cancellation is
`lean/YMGap/Constructive/CauchyConv.lean:56`, `Q'.mul_eqv_zero_of_pos`.
The reference w=2 is NOT a physical nome or a replacement original action.
No division by an unknown state norm or spectral measure is used.

Observed verification: focused overlap check 1 PASS, exit 0; all four public
printed gates use only {propext, Quot.sound}. Root read the entire changed
source and actual called APIs; independent COMPLETE frozen 239-line source
mathematical review PASS. The launch followed a fresh successful conflict/
memory preflight, one capped 20-GiB worker, 12-GiB reserve and zero swap.
No root/full-tree build or axiom audit; no new sorry, analytic input, module,
frontier weakening or scorecard closure.

    source SHA256 2df0970448548c753a6f57ace9fb5a0b3848650bf5428b1159a888b377ca95e7
    /private/tmp/ym-oct8-family-loop-orthogonal1.log
    log SHA256 179a70afce55d2023a53248bda43b6f14c51c55bb134fe7c08222dc8d4ac303e

### Decision and actual consumer

PRUNE only the geometry-only bare-Haar overlap join. Spatial coefficient
averaging does not change the whole family's bare w^12 eigenimage, and its
bare overlap with the proposed larger square trial is exactly zero.

The ORIGINAL trial bound
`lean/YMGap/Continuum/BF4DyadicWilsonSquareLoopModeReserve.lean:159`,
`paddedSquare_transfer_loop_mode_floor`, still applies to arbitrary supported
signed h, but its moments are weightedMass(h) and weightedMass(h*F).
`weightedMass` retains the full original spatial action; an actual family
source additionally retains its terminal message and original transmission.
The checked zero above cannot be substituted for either weighted moment.
The OWN-centered loop-cost specialization at `:217`,
`paddedSquare_own_block_cost_loop_reserve`, uses its OWN long-loop source,
not the current plaquette family's centered source. That source is not
silently substituted here. A useful family reserve still needs actual
action-generated/transmitted overlap relative to its OWN surviving variance
and BOTH chronological masses.

The direct alternative remains
`lean/YMGap/Continuum/BF4WilsonAllNomePositiveOrbitResponseOrder.lean:696`,
`signedOrbit_response_credit_identity`: pay its COMPLETE original signed
right-hand side, including negative early covariance, rather than infer
survival from late-credit positivity or from bare geometric trials.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedPredictionPayment.lean:505`,
`blockConditionalRatio_noiseCost_abs_le`, still provides the actual cost/noise
approximation, not the missing relative innovation ceiling.
CONTINUE these action-specific producers; no extra overlap assumption bundle
or conditional compiler is added. Interacting survival, rate control,
physical calibration, continuum/QFT, every group and Clay remain OPEN.
Canonical displayed proof/expansion claims are unchanged; no chart reprint.

## Sharper finite near-flat curvature and endpoint route screen (2026-10-08 UTC)

This is a mathematical estimate and a screen of a particular allowance,
not another conditional frontier interface. The normalized finite Jacobi
heat is retained literally; it is not the original unweighted character
prefix or the interacting terminal marginal.

### Produced estimates

`lean/YMGap/Continuum/JacobiHeatNearFlatLogHessian.lean:115`,
`heat_first_le_cap`, proves h'<=C_T*h on X>=0 for every finite prefix,
including N=0/1, with C_T=2*w/(1-w*w) and strict 0<w<1. Actual heat value
and first-jet moment pins are used; no heat inverse is formed.

`lean/YMGap/Continuum/SU2QuaternionPairedPrefixCostScaling.lean:182`,
`normalizedPairedPrefixCost_transverseResidual_lower`, gives

    6 <= 3*(1-w)*(C_prefix-C_T).

Its `jacobi_identity_curvatureResidual_lower` at :208 gives the stronger
screen with the actual finite heat value and derivative at relative X=1:

    6*h^2 <= 3*(1-w)*(C_prefix*h^2-h*h').

The paired angular contribution at that endpoint is -h*h'. Thus even its
maximum produced cancellation cannot pay THIS selected global envelope.
The actual consumer being screened is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalLocalSignedGram.lean:649`,
`terminal_local_signed_score_bound`. Its source-marginal Hessian is NOT
identified with the kinetic heat Hessian by this estimate. Tighter local
allowances, signed Ward payment and Yang--Mills are not refuted.

The new `lean/YMGap/Continuum/JacobiProductRadialNearFlatBound.lean` instead
produces a smaller positive-hemisphere cost. With c_i=w^(2*i+1),
r_i=2*c_i/(1+2*X*c_i+c_i^2), and

    H_i = X*r_i+(1-X^2)*r_i^2,
    F(c,X) = 2*c*(c+X)/(1+2*X*c+c^2),

its `radialSummand_telescope` (:118) proves

    (1-w^2)*H_(i+1) <= F(c_i,X)-F(c_(i+1),X).

For r=w^2, the positive cleared numerator is

    2*(1-r)^2*c *
      [c*(1+2*r-r^2*c^2)+X*(1+r*(r+2)*c^2)+2*X^2*r^2*c^3].

The exact multiplier is D(c,X)*D(r*c,X)^2, strictly positive under the
stated guards. Finite summation retains the terminal potential; H_0<=1
and 0<=F<=1 supply the explicit endpoint budget. No telescope or recurrence
is assumed. `productRadialCost_cleared_le` (:260) and
`productRadialCost_le_nearFlatCap` (:308) prove, on 0<=X<=1,

    (1-w^2)*D_N(X) <= 2-w^2,
    D_N(X) <= C_local := 1+1/(1-w^2),

for EVERY N, including zero. `nearFlatCap` (:303) is computed Type-level
rational data, not an existential or opaque constant. The cost is uniform
in finite N on this hemisphere; its dependence on w remains EXPLICIT.

`heat_radial_nonnegative_nearFlat` (:336) directly fills the existing
`lean/YMGap/Continuum/JacobiHeatRadialMomentJets.lean:305`,
`heat_radial_nonnegative_of_productCost`, with this produced ceiling:

    C_local*h^2+(1-X^2)*(h*h''-h'^2)-X*h*h' >= 0.

All three jets belong to the SAME inverse-nome/half-normalized finite
Jacobi heat evaluated at 1+X. No product-ceiling hypothesis is left in the
new consumer; no Haar/original-prefix/interacting certificate is asserted.

### Verification evidence

Final slope check 1 and global-envelope endpoint check 2 PASS, exit 0.
All six/seven printed gates respectively remain within {propext, Quot.sound};
the gated computational definition is axiom-free. Complete frozen independent
source reviews PASS for both. Original cost check 1 failed only at a
multiline match layout; the corrected final source is the checked version.

    slope source SHA256 dd2a890eca126f7b9ed68c66d36f922bd1f1d254c351a86a2878f557760d811d
    /private/tmp/ym-oct8-nearflat-slope1.log
    log SHA256 8fc6c146e2a287eb4827f07838af0dcac455deee3ea2bd64808acebd791535d6

    global-screen source SHA256 819cbfe98b051f1ede5dbab69e1e02a9a8ade9745a093ff19350b50387746c56
    /private/tmp/ym-oct8-endpoint-allowance2.log
    log SHA256 f55d4d27ba4a1a4c14207cc3b45f5d2890290cfbc1429facfdf86d3634cc6bcd

Finite product check 2 PASS, exit 0; eight gates permitted. Check 1 exposed
only a default-depth issue for the closed reflected polynomial identity and
missing type ascriptions on four closed constant positivity proofs. The final
identity uses `decide +kernel` (Lean 4.29.1 kernel proof construction), NOT
native evaluation; no recursion/heartbeat/memory limit was raised. Root also
reproduced the exact integer polynomial identity diagnostically; only the
Lean proof is certification. Final 359-line source includes the direct
heat-jet consumer, has COMPLETE independent source review PASS, and its
focused check 3 PASS, exit 0, with all ten gates permitted. Both computed
potentials/caps are axiom-free; proofs use at most {propext, Quot.sound}.

    final local source SHA256 fd1de04e7af49b522e56deedb49a39dbaae6a6ccc2a575027c8ae1d3de7c1231
    /private/tmp/ym-oct8-local-product-curvature3.log
    log SHA256 98fb2bc4d82e9a415a96b716f30886835b923fe537dd89109735546ac3915501

Every launch had a fresh SUCCESSFUL live conflict/memory preflight, one
20-GiB worker and 12-GiB reserve; observed swap was zero. An initially denied
sandbox process inspection was retried read-only with approval BEFORE any
launch. No new sorry, axiom, Classical premise, native proof, frontier
weakening, or limits increase. Root registration only; no root/full-tree
build, guard sweep or axiom audit. Three user-owned duplicate Lean files
remain untouched and outside the checkpoint.

### Continue / prune and the smaller unpaid step

PRUNE kinetic endpoint payment of the selected GLOBAL envelope alone.
CONTINUE the genuinely sharper local telescope and its actual heat jets.

The next bounded PAPER proposition (independently derived by root and two
reviewers, NOT yet Lean proved) is

    C_local*h-h' <= (15/4)*h at X=1,
    provided w^(2*N+1) <= 1-w.

At X=1, F(c)=2*c/(1+c); a second elementary finite difference gives
M1(1)>=w^2/(1-w^2)*(F(w)-F(w^(2*N+1))). The diagonal estimate is
M2(1)<=M1(1)/2. These yield the stated no-inverse target, including zero
and constant heat prefixes. The actual tail can be produced with
`lean/YMGap/Continuum/HeatKernelConvGen.lean:266`, `powBaseCutoff`,
`:275`, `pow_base_le_cutoff`, and :229, `pow_base_antitone`; an existing
application pattern is `JacobiHeatRadialProducedBound.radialOnset_small_factor`
at `lean/YMGap/Continuum/JacobiHeatRadialProducedBound.lean:34`.
The growing cutoff as w approaches one is explicit, not hidden uniformity.

For 0<=X<=1, summand monotonicity and the already checked M2<=M1 predict
the PAPER band bound C_local*h-X*h'<=[17/4+(1-X)*C_local]*h. This does
not control the radial log-Hessian term or the interacting marginal by
itself. Neither PAPER inequality is counted as a checked proof.

Still OPEN: an ORIGINAL local curvature certificate and finite-prefix
deficit transport, the original-source weighted complement/concentration,
and complete signed payment relative to OWN surviving variance and BOTH
chronological masses. A scalar near-identity cancellation does not pay
posterior score variance or silently supply the missing interacting input.
The whole-project continuum/QFT/physical-mass/every-group target remains
OPEN. Canonical displayed claims are unchanged; no chart reprint.

## Checked endpoint cancellation and global sharper radial certificate (2026-10-08 UTC)

Previous goal turn: PROGRESS (`007c8b78`, actual finite telescope/heat consumer
and global-envelope obstruction, pushed). This turn completes the bounded
endpoint test and a shorter global comparison, not a restated inventory.

### Exact mathematical contraction

`lean/YMGap/Continuum/JacobiProductRadialNearFlatBound.lean:381`,
`endpoint_sTerm_telescope`, proves

    w^2*[F(c_i)-F(c_(i+1))] <= (1-w^2)*r_i,
    F(c)=2*c/(1+c), c_i=w^(2*i+1), r_i=2*c_i/(1+c_i)^2.

The positive cleared remainder is 2*c_i*(1-w^2)^2. The actual finite
moment telescope retains F(c_N). With c_N<=1-w, the explicit positive
slack (1-w)^2*(8*w^2+15*w+5) gives `endpoint_firstMoment_payment` (:504),
4*C_local<=4*M1+13. `endpoint_secondMoment_twice_le_first` (:602) proves
2*M2<=M1 from the literal factor bound. Actual nonnegative normalized
product/heat pins, WITHOUT inverting either heat or M1, then yield

    C_local*h-h' <= (15/4)*h at X=1.

This is `heat_endpoint_cancellation` (:619), not an interacting marginal
identity. `endpointCancellationOnset` (:685) computes
HKConvGen.powBaseCutoff w (1-w); its tail theorem (:687) fills
`heat_endpoint_cancellation_at_onset` (:697). N=0/1 are retained when
their stated guards hold. Strict 0<w<1 and the cutoff dependence remain
explicit; no beta/spacing-uniform gap is asserted.

The existing `lean/YMGap/Continuum/ThetaProductRadialCeiling.lean:49`,
`productRadialCostCReal_le_endpoint`, ALREADY bounds the SAME completed
cost everywhere on [-1,1] by its endpoint cost. The new finite endpoint
ceiling applies to every actual CReal approximant; `productRadialCostCReal_at_one_le_nearFlatCap`
(:140) passes it to the constructed limit. `productRadialCostCReal_le_nearFlatCap`
(:150) composes the existing global comparison, and
`productRadialCost_le_nearFlatCap_add_tail` (:164) returns

    D_N(X) <= C_local + radialTailPayment(w,N),   -1<=X<=1,
    C_local=1+1/(1-w^2),   c_N<=1/8.

Both scalar endpoints and the signed finite tail remain. This is
weak-coupling-sharper; it need not improve the old cap at every nome.
It needs NO hemisphere support or southern-complement estimate for this
PRODUCT step. That narrows the earlier backward warning: the original law
still has no hemisphere-support producer, but none is required here.

`lean/YMGap/Continuum/JacobiHeatRadialProducedBound.lean:100`,
`heat_radial_nonnegative_nearFlat`, feeds this produced cost into the
actual three-heat-jet consumer on the WHOLE interval. Its computed cost is
`nearFlatRadialCap` (:33), not an assumed scalar ceiling.

`lean/YMGap/Continuum/JacobiHeatRadialHaarCertificate.lean:217`,
`radialPolynomial_nearFlat_strict_margin`, adds positive slack delta and
uses the SAME actual nonempty-prefix heat floor to produce delta*floor(w)^2.
`nearFlatRadialCertificate` (:241) computes Bernstein rows and returns the
actual Type-valued Certificate of the literal substituted radialPolynomial,
for any supplied certified unit-square coordinate. No margin/reconstruction
or target-positivity premise is assumed. Its 1<=N, c_N<=1/8, delta>0 and
strict-nome guards are retained. The floor affects construction precision,
not an inverse multiplier in the curvature cost.

### Observed verification, not predicted status

Four final focused checks ALL PASS on first launches, exit 0, with 21/9/9/7
printed gates respectively. All reported axioms lie in {propext, Quot.sound};
the gated computational caps/potentials/onsets are axiom-free. Root inspected
all changed source and actual APIs; independent COMPLETE frozen final-source
mathematical reviews PASS at every hash below.

    endpoint source SHA256 00c507ddd43879bea5a3f7195973f7d4261ebeb81097c09f5cc486f389cf9ff5
    /private/tmp/ym-oct8-endpoint-cancellation1.log
    log SHA256 9edfcf4eebefae79111ae60f00c1100767de143cc166c16d9239e64215a90ae1

    global ceiling source SHA256 6709c54a96e11b4d6d8337daefc83ec53f6e74fd4927632e7c967f190fa1ca9a
    /private/tmp/ym-oct8-global-nearflat-ceiling1.log
    log SHA256 723c32abcdcbd86a0ebbd207c0022ebb85d497ec092819d8ab81ddb2d24e171c

    actual heat source SHA256 35eb345944e89051876b33b36e56357dee6a15f6be2cd8600184df13f878ed80
    /private/tmp/ym-oct8-global-nearflat-heat1.log
    log SHA256 b24893653a5c112bfe569e6f83b4b7d812474f1c8dc273b4c59deae04ba61243

    radial Haar source SHA256 4a75c95fec1e0ee2a22abfcab1c4f92a669255725dd7a6b2e1538d62a4f0d3b1
    /private/tmp/ym-oct8-global-nearflat-haar1.log
    log SHA256 6fbbfd5310c2509b92f0fcfa177e2a8068d9e7655d30e2372754a0e07489bc60

One compiler at a time, one 20-GiB worker and 12-GiB reserve after EACH
fresh successful live conflict/memory preflight; observed swap zero.
No new resource-option increase, sorry, axiom, Classical/native proof,
frontier weakening or original-object substitution. The older local heartbeat
annotation in the unchanged theta theorem was not raised. No root/full-tree
build, guard sweep or axiom audit. Existing public statements are unchanged;
no new module or frontier enumeration. User-owned duplicate files untouched.

### Decision and primary-source benchmark

CONTINUE the actual original join: reuse the existing full frozen-direction
reconstruction, then original character-prefix value/first/mixed-jet deficit
transport and explicit precision. The new radial Haar witness is produced,
not an open analytic input. Complete original signed innovation/window cost
relative to OWN surviving variance and BOTH chronological masses remains
OPEN. A global scalar curvature allowance is not that joint payment.
The broader 17/4 local-band slope statement remains PAPER; its hypothetical
localization is not made a prerequisite for the now-checked global route.

A parallel targeted PRIMARY-source check found Hamilton's Corollary 4.4,
p.125, [A matrix Harnack estimate for the heat equation (1993)](https://intlpress.com/site/pub/files/_fulltext/journals/cag/1993/0001/0001/CAG-1993-0001-0001-a006.pdf).
It gives a global lower log-Hessian bound on a compact manifold with
nonnegative sectional curvature and parallel Ricci, for a positive heat
solution. The publisher-indexed original text was inspected; direct PDF
fetch returned 403. With the unit-S3 normalization in
`docs/CONVENTIONS-COUPLING.md`, its time is s=t_carrier/4=-log(w), and
its coefficient is 1/(2*s), NOT 1/(2*t_carrier). It is a benchmark for the
completed kernel, not a theorem about finite prefixes or our interacting
marginal. No PDE theorem or classical proof was imported or assumed: the
actual constructive global comparison already present in this repository
made that detour unnecessary for this bound. Continuum/QFT, physical mass,
every compact simple group and the unchanged Clay goal remain OPEN.
Canonical displayed claims are unchanged; no chart reprint.

## Next bounded original-prefix contraction (2026-10-08 UTC)

Previous turn: PROGRESS (`d7eafaaa`, four checked leaves and actual radial
certificate; review reconciliation `19ae7ef1`; both pushed). Selection
before verification: produce full frozen ORIGINAL-prefix curvature at
`4+1/(1-w^2)`, with a computed cutoff/tolerance. Inputs are the actual
near-flat radial certificate, existing full frozen reconstruction, exact
original value/first/all-nine mixed-jet deficit pins and original heat floor.
The tail is charged before selecting precision: require BOTH c_N<=1/8
and c_N<=(1-w^2)/4, which pays the literal radialTailPayment<=1.
The former does not follow from the latter at every strict nome. Weighted
slack one and approximation slack one then give the stated cost; six-column
matrix error is paid by quarter-floor precision, not a dimension cost.

Actual consumers: `SU2QuaternionPairedHeatAtFrozenCurvature.heatAt_frozen_curvature_certificate`
and `BF4ExactSlabFixedSpatialTerminalLocalSignedGram.terminal_local_signed_score_bound`.
They must keep the SAME original action, arbitrary supported frozen directions,
all ordered mixed jets, OWN center and terminal density. Predicted outcome:
a smaller produced original-prefix allowance, NOT an upper innovation or
physical gap. Tests: strict nomes approaching zero/one, N=0/1 guarded,
arbitrary zero/repeated/signed directions. Budget: changed focused leaves
only, serial 20-GiB worker/12-GiB reserve with fresh live preflights and
independent complete final-source review. Abandon/revise any attempt to
reuse an unjustified old cutoff, discard signed deficits, or replace the
original law by kinetic heat. Mathematical selection checked independently;
new Lean proof status awaits focused checks. No chart-state change.

### Observed: original-prefix and original terminal joins checked

The selected mathematical contraction is now CHECKED, not a supplied cost
interface. The exact sharper fixed-nome allowance is the computed rational
`nearFlatPrefixCurvatureCost = nearFlatCap+3 = 4+1/(1-w^2)`.

- `lean/YMGap/Continuum/JacobiHeatPrefixCurvaturePrecision.lean:86`,
  `nearFlatRadialOnset`, computes the max of the actual eighth onset and the
  power cutoff at (1-w^2)/4. `nearFlatRadialOnset_tail_le_one` (:100) pays
  the literal 4*c_N/(1-w^2); `nearFlatRadialCap_le_curvatureCap` (:135)
  bounds weighted cost plus one by `nearFlatCurvatureCap` (:65).
- `lean/YMGap/Continuum/SU2QuaternionPairedFrozenJacobiCurvature.lean:152`,
  `frozen_curvature_nearFlat_certificate`, constructs the actual full frozen
  heat certificate from the produced radial witness, retaining all nine jets
  and the favorable cross-product-square/log-discriminant complement.
- `lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixCurvature.lean:186`,
  `prefix_frozen_curvature_nearFlat_certificate`, consumes the exact SAME
  original value/first/ordered mixed-jet deficit pins and actual head floor.
  The quarter-floor precision pays the six-column error; floor dependence is
  confined to precision, not an inverse coefficient in the cost. New tolerance
  (:172), cutoff (:177) and cost (:181) are computed Type-level data.
- `lean/YMGap/Continuum/SU2QuaternionPairedHeatAtFrozenCurvature.lean:237`,
  `heatAt_frozen_curvature_nearFlat_certificate`, transports this certificate
  to any distinct selected pair's FIRST endpoint after taking the actual jets.
  Supported Haar equality and the reverse chart return the literal heatAt.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalLocalSignedGram.lean:799`,
  `terminal_local_signed_score_bound_nearFlat`, now constructs the local
  curvature input to the actual original terminal signed Gram. The density is
  STILL localOutputDensity*a with a=terminalMessage(n+r); q*P equals
  lastStepAction*a. A=T(a), B=T(a*phi), all nine DDA jets, the actual noise
  A*T(a*phi^2)-B^2 and the negative DA^2 term remain unchanged. No termwise
  positive Hessian, upper innovation, norm floor or conditional-law replacement
  is assumed. Arbitrary supported signed phi permits original rational centers.

Private arbitrary-cost reconstruction/recoding/moment helpers reuse the SAME
existing proofs; old public types and guards are unchanged. Public sharper
instances PRODUCE their certificates and use their NEW computed cutoff.
The strict nome, nonempty weighted prefix and distinct-pair/support guards
remain; no zero direction or signed observable is discarded. No new import,
module, axiom, sorry, classical/native proof, resource option or frontier
weakening. Complete independent mathematical FINAL-source reviews PASS at
every hash below; root inspected all changed proofs and actual consumers.

Five final focused targets PASS, exit 0, with 21/5/11/5/15 printed gates.
All observed axiom sets lie within {propext, Quot.sound}. Precision check 1
failed ONLY to infer the reciprocal denominator in an untyped local `have`;
check 2 fixes its type explicitly and removes the failed elaboration's
sorryAx. No sorry appears in source or in any final successful gate output.
The other four checks passed on first launches. Existing unused-variable
warning in the precision API was unchanged.

    precision source a11da2a89c48c4adfed0ebd12f056f0d3cda96f755d197acb1415c6311aec152
    /private/tmp/ym-oct8-sharper-prefix-precision1.log FAIL
    SHA256 a6a01e0e7b906b488b0c1dbddd4b213f96a7c518a9b952dc6ab1de1acdea8769
    /private/tmp/ym-oct8-sharper-prefix-precision2.log PASS
    SHA256 cafda7908f82ead14dd4d8a75eef732f4e90f64399766b518981f1b68ea41ba2

    frozen heat source 32783d59e175df0b776b6a76c2f4ad25beee7da99c9801dff0ac75848d7ff5ef
    /private/tmp/ym-oct8-sharper-frozen-heat1.log PASS
    SHA256 7c103c2621eba14b471d4add794bf80a8082a685195cc15e3ecc4a4e359db261

    original prefix source a75b73dea3bdfd744ce98eae9919f9c9bc881990cf61aee37c84866e95368c42
    /private/tmp/ym-oct8-sharper-original-prefix1.log PASS
    SHA256 0e8bd0e50f50f13cebb50ea6d8bb0515d2d3f10618aa9909bbbe28e534055f46

    selected pair source a710e517b1f486e53c7bd295a9259ae4cdece93394b403060612f7132343fed4
    /private/tmp/ym-oct8-sharper-selected-pair1.log PASS
    SHA256 02c54879f302ee248c0baf8d07770c5e9e62d96dd150f733b7fd4dec6924934e

    original terminal source d438da0739d7d8855bb9e6e43f3999fc0f5b3298c5ee99c4f89d46f11efe83d6
    /private/tmp/ym-oct8-sharper-original-terminal-gram1.log PASS
    SHA256 cb4be337c96e09a32560dff96d3c2e65cd474e8417daa4b612e806ce59fac291

Safety: serial monitored 20-GiB worker, 12-GiB OS reserve after EACH successful
fresh live conflict/memory preflight; observed 84--85% pressure-free, zero
swap. Initial sandbox-only host reads were denied, so no check launched from
that incomplete preflight; permitted read-only host inspection succeeded
before every launch. No lock bypass/removal, limits increase, broad tests,
root/full-tree build or axiom audit. User-owned duplicate files untouched.

Decision: CONTINUE actual Ward/signed payment with this sharper original
terminal Fisher, retaining its signed Hessian, negative DA square and the
original density/spatial/weight contributions together. The local allowance
still depends on nome and diverges near one; it is NOT a useful completed
innovation reserve by itself. Complete signed cost relative to OWN surviving
variance and BOTH chronological masses remains OPEN. Nontrivial continuum
survival, physical calibration, full QFT structure, every compact simple group
and the unchanged Clay target remain OPEN. No canonical field or displayed
chart state changes, hence no chart reprint.

## Decision test: can finite reciprocal credit fund retention? (2026-10-08)

Previous turn: PROGRESS (`86964175`, independently reviewed paper selection
and actual-source correction, pushed). The next mathematical test concerns
the ACTUAL favorable Ward reciprocal contribution, not another reassembly.
For fixed original terminal A, original F=Vbar^2*matchedNoise(a,phi), and
outgoing degree k+1, prove its Haar credit tends to zero at an explicit
onset. Incoming phi/approximation degree stays fixed independently.
Inputs: original positive terminal window, produced favorable certificate,
exact derivative of A*G, residual interval/cancellation and existing
polynomial-geometric decay. Cleared target:

    ell*H[F*G*(JA)*J(A*G)]
      <= (k+1)*(1/upper)*rho^k * H[F*(JA)^2],
    rho=1-ell/upper<1.

The identity rho^k-(AG)*E_k=(rho^k-E_k)+E_k*E_(k+1)
constructs its sign; no inverse terminal lower floor is put into a
certificate. The lower window pays ell*credit<=A*credit. A computed
polynomialCutoff at ell*epsilon then returns credit<=epsilon.
Actual consumer being screened: the positive term discarded by
`RatioNoiseWardAbsorption.original_ratioNoise_ward_absorption_le`;
the desired relative reserve still belongs to
`WindowSignedCost.original_window_budget_macro_ratio`.
Prediction: PRUNE paying a nonzero outgoing-degree-uniform reserve solely
by this finite reciprocal credit; retain finite-degree credit and joint
absorption/density/spatial payment. This is not a refutation of original
survival or of a justified coordinated changing-family estimate.
Tests: zero source/cost, rho=0, k=0/1, arbitrary signed phi and depth zero;
strict nome and actual cutoff/support/window guards remain. Budget: two
changed focused leaves only, one monitored 20-GiB worker/12-GiB reserve,
fresh conflict/memory preflight before each check, independent complete
final-source review. Revise if a source/window is silently replaced or
incoming/outgoing degrees identified; abandon generic wrapper work without
the actual terminal instance. No new sorry, analytic premise or chart claim.

### Observed: reciprocal-credit-only reserve is pruned by checked decay

Both selected focused leaves now PASS, exit 0. The actual mathematical
increment is a degree-decaying bound and computed all-later tolerance,
NOT just the previously available nonnegative sign.

- `finite_reciprocal_favorable_cleared_le`,
  `lean/YMGap/Continuum/QuaternionHaarFiniteReciprocalHessianSign.lean:244`,
  proves the cleared bound above from the actual gap certificate. No
  inverse of ell is introduced. `favorableCreditCutoff` (:326) computes
  its onset from the EXACT moment H[F*(JA)^2], and
  `finite_reciprocal_favorable_tolerance` (:334) cancels positive ell.
- `originalRatioNoiseCreditCutoff`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:440`,
  computes the actual terminal/noise onset. The lower/upper windows and
  F=Vbar^2*matchedNoise are produced from the original action, not assumed.
  `original_ratioNoise_reciprocal_credit_tolerance` (:458) instantiates
  the bound, retaining supported signed phi and all original factors.
- `original_ratioNoise_reciprocal_credit_no_eventual_floor` in that file
  (:504) proves that at ANY proposed onset no positive delta can be an
  eventual floor for this credit. It chooses max(onset,cut(delta/2))
  constructively; no classical alternative or spectral argument is used.

Incoming phi and its approximation degree remain fixed independently of
outgoing k. Zero cost/radius, k=0 and terminal depth zero are retained;
there is no source/noise normalization division. This does not prohibit
finite-degree credit, coordinated changing-window precision, useful
payment by the absorption square, or survival under the complete original
signed estimate. No actual physical mass-gap claim is contradicted.

All 15 final printed gates (6 core, 9 actual consumer) are within
{propext, Quot.sound}; no sorryAx, compiler error or warning in final logs.
Complete independent 373/545-line source review PASS before repairs, then
final-hash repair review PASS. ROOT inspected the complete changed proofs
and their existing certificate/consumer context. First core launch failed
ONLY multiline pattern syntax in the scalar normalization; second passed.
First actual launch passed the tolerance proof but failed two helper names
in the no-floor contradiction; second uses existing strict transitivity
and Int.lt_irrefl and passed. No statement or guard changed in either repair.

    core source b23b51a41446937f486aea96424e21022ba3c65aa9569b8ff99f3d0d3afe3148
    /private/tmp/ym-oct8-reciprocal-credit-decay1.log FAIL
    SHA256 6da52286d34b83c9aa8fd9d749148ab40b4b81f1e134abb2784f2ef60f60ade3
    /private/tmp/ym-oct8-reciprocal-credit-decay2.log PASS
    SHA256 642e987f720c3cf8918c1af9845233d2fc63ffc9642f55ef77e3f02988875331

    actual source 3cb423126e21a67761891c3d0c6731e4de8f188acaa04af9ee8a405eaaad81b5
    /private/tmp/ym-oct8-original-reciprocal-credit1.log FAIL
    SHA256 2f7d6c5e65179d4b2bfbb5c5b0c1bbe128390a865c47855e86ff9a795507d001
    /private/tmp/ym-oct8-original-reciprocal-credit2.log PASS
    SHA256 c148cdcd6169e0638abdd81c9ae660b8bc4fc151e855aeff5c1396388a05fdec

Fresh successful live conflict/memory preflight before EVERY launch;
one monitored 20-GiB worker, 12-GiB OS reserve, observed 84--85% free
and zero swap. All processes terminal. No full build/audit, lock bypass,
limit increase, foreign execution, new module/frontier or new analytic
premise. Existing APIs/fields and user-owned duplicates remain unchanged.

Decision: PRUNE persistent reserve from reciprocal credit ALONE at fixed
source/window. CONTINUE the actual absorption square TOGETHER with signed
density/spatial payment, against OWN surviving variance and BOTH masses.
The complete changing-family signed bound, continuum survival, physical
calibration, QFT structure, every compact simple group and Clay remain OPEN.
Displayed canonical claims are unchanged; no ASCII chart reprint.

## Decision test: center the actual absorption square (2026-10-08)

Previous goal turn: PROGRESS (`2f314b38`, checked original reciprocal-credit
decay and no eventual floor, pushed). Test a genuinely smaller positive
payment, not another integration-by-parts reassembly. With the ORIGINAL
W=Kkin*S*a, A=T(a), B=T(a*phi), X=A*phi-B, t=Jphi,
m=T(a*t), E=T(a*t^2), D=JA and nu=A*T(a*phi^2)-B^2, put
Y=D*X+A^2*t. Actual conditional integration gives I[W*X]=0 and
I[W*Y]=A^2*m. The centered square should produce

    I[W*(Y-A*m)^2] = A*[nu*D^2+2*A*D*M+A^2*(A*E-m^2)],
    M=I[W*X*t].

Positive-window reflection can therefore replace A^3*E by
A^2*matchedNoise(a,Jphi) in the ORIGINAL absorption bound. Its actual
consumer is `RatioNoiseWardAbsorption.original_ratioNoise_ward_absorption_le`;
the produced multiplier-square cap should then leave only
H[Vbar^2*matchedNoise(a,Jphi)] in the positive payment, not
H[Vbar^2*A*T(a*(Jphi)^2)]. Keep signed density and spatial corrections.
Predicted outcome: a smaller actual cost, NOT a paid changing-family reserve.
Test constant/zero signed phi, d=0, arbitrary outgoing degree including zero
for the cap and independent incoming degree. No inverse or supplied score
variance, stationary law or cross-mass equality. Budget: two existing focused
leaves, one monitored 20-GiB worker/12-GiB OS reserve after each successful
live preflight, independent complete final-source review. Revise if any
original factor is lost; stop if the result only restates the old second
moment or assumes the needed subtraction. OWN variance/BOTH masses and all
physical/Clay frontiers remain OPEN; no new analytic premise or chart claim.

### Observed: the ORIGINAL positive payment is gradient noise, not full energy

2026-10-08 19:35 UTC. Two focused checks PASS on their FIRST launches,
exit 0, and independent COMPLETE final-source mathematical review PASS.
The centered-square identity above is now checked, not merely PAPER.

- `residual_mean_pin`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseGradientAbsorption.lean:195`,
  produces the literal zero incoming residual mean. Its private
  `centered_absorption_square_pin` (:222) retains every W factor and
  subtracts A*m, not an independently chosen center.
- `original_ratioNoise_phiGradient_noise_absorption_le` in that file
  (:371) produces the smaller A^2*matchedNoise(a,Jphi) payment under every
  certified output insertion. The actual terminal window cancels only one
  positive A in Haar order; no density/noise inverse or new premise is used.
- `original_ratioNoise_ward_noiseGradient_le`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:304`,
  feeds this estimate into the SAME outgoing reciprocal Ward calculation.
  The shared private signed calculation preserves the old public Ward type.
- `original_ratioNoise_noiseGradientPayment_unit_le` (:449) uses the
  produced noise and multiplier-square certificates to remove (A*G)^2
  ONLY from the positive payment. `original_ratioNoise_ward_unitNoiseGradient_le`
  (:515) therefore leaves H[Vbar^2*matchedNoise(a,Jphi)], while both signed
  density and twice-spatial corrections keep their exact successor G.
- `original_ratioNoise_noiseGradientPayment_weighted_pin` (:616) proves
  the actual original-law pullback

      H[Vbar^2*matchedNoise(a,Jphi)]
        = weightedMass[a*(Jphi)^2*T(Vbar*A)]
          - H[Vbar^2*(T(a*Jphi))^2].

Thus a real predictable-gradient square is no longer overpaid. This is a
smaller positive cost, not a sign or useful relative bound for the complete
signed expression. Arbitrary supported signed phi, d=0, zero source/noise
and all output precision are retained; cap degree zero is included, while
Ward still uses a successor. Incoming phi/degree and outgoing degree are
independent. All old public statements/guards remain unchanged.

Independent reviewer read the COMPLETE 516-line producer and 770-line
Ward consumer, including the original-law pullback and shared calculation.
Two match layouts were repaired BEFORE compilation without changing the
mathematics or statements. ROOT inspected all changed proofs and context.
All 17 final printed gates (4 producer, 13 Ward) are exactly
{propext, Quot.sound}; no sorryAx, error or warning in either final log.

    producer source aa4345799740c70606528c918d36806b9511bec056730ca561960563e9267589
    /private/tmp/ym-oct8-centered-gradient-absorption1.log PASS
    SHA256 467f1eb0223da0ee21e7fae4cf03f50029686216cada40ee62f077c4173c5060
    Ward source bb522669a63584a08f6a86758060a60e92fc2cbde68075c2bdc0597cf627ca22
    /private/tmp/ym-oct8-centered-gradient-ward1.log PASS
    SHA256 a4071f507568223ef56a4fcac73048b11b13da99a9faf2c9abb51057a5dd6a5a

Fresh successful conflict/memory preflight before EACH launch; one serial
20-GiB worker/12-GiB OS reserve, observed 85--86% free and zero swap.
Both process handles are terminal. No root/tree build/audit, limit increase,
lock bypass, new module/frontier, foreign code or new analytic premise.
User-owned duplicate files are untouched. No canonical atom is closed.

Parallel scoped screens did NOT supply an additional uniform estimate:
the original integrated-score instance has weight S*g_n*g_(n+1), whereas
this square uses the full doubled Kkin*S*a. Applying the generic centered
score bound to X^2 would require its fourth-moment determinant, not just
the existing noise (see `integratedAngularScore_certificate`,
`lean/YMGap/Continuum/SU2QuaternionIntegratedScoreVariance.lean:147`, and
`original_marginal_integratedScore_certificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialIntegratedScoreVariance.lean:59`).
The qualitative all-plane zero-square screen gave no quantitatively new
original-law bound beyond global fixed-volume min/max; it was not selected
for implementation. Neither screen becomes a new prerequisite.

Decision: CONTINUE from the centered gradient-noise payment, keeping its
negative transmitted square JOINTLY with signed original density/spatial
corrections. The backward consumer remains
`original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`:
complete changing-family cost against OWN surviving variance and BOTH
chronological masses. That estimate, continuum survival, physical mass
calibration, full QFT structure, all compact simple groups and Clay remain
OPEN. Displayed chart claims are unchanged; no chart reprint.

### Selected experiment: squared-residual variance under the SAME conditional law

2026-10-08 UTC. Previous goal turn: PROGRESS in targeted paper selection
and authoritative plan, not a new mathematical closure. Return to the
existing signed-payment consumer rather than add a literature branch.

Exact proposition: for W=Kkin*S*a, A=I(W), b=I(W*phi),
X=lift(A)*phi-lift(b) and nu=A*I(W*phi^2)-b^2, produce the certificate

    det_W(X^2) <= 4*C^2*A^4*nu - A^2*nu^2.

Available inputs: original positive W, finite head integration and its
variance certificate; `blockConditionalRatio_squareCertificate`
(`BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:233`) supplies
C^2-phi^2, and its literal OWN-padded-square instance (:368) supplies C=17.
The short inverse-free identity is

    4*C^2*A^2-X^2
      = 2*A^2*(C^2-phi^2) + 2*(C^2*A^2-b^2) + (A*phi+b)^2.

Conditional positivity produces the second cap, rather than assuming it.
Multiplying by W*X^2 and integrating preserves the negative nu^2 term.
Actual algebra consumer: `conditionalGrussSquare_certificate`,
`SU2QuaternionConditionalGrussSquare.lean:76`, with test X^2. It must
retain L^2*A^2-I(d)^2 and the centered signed moment for d=Kkin*J(S*a).
The available `endpointSourceRelativeBound`
(`BF4ExactSlabFixedSpatialEndpointRelativeBound.lean:80`) controls S*a
under its explicit nome-dependent cutoff, including depth zero; multiply
its actual signed tilts by the same positive kinetic factor. Do not
substitute the different odd-marginal integrated-score instance.

Predicted useful output: an actual conditional density-covariance square
bound for supported signed bounded phi, with explicit nome cost and actual
OWN-padded instance, not an assumed variance bound. Ultimate consumer stays
`original_ratioNoise_ward_unitNoiseGradient_le` (WardAbsorption :515),
then `original_window_budget_macro_ratio` (WindowSignedCost :245).
Cutoff compatibility and useful changing-family payment remain to be proved.
Test zero heads/tail/source/noise, zero cap and all degree/depth values;
incoming and outgoing reciprocal degrees remain independent. Verification
budget: two narrow leaves, one serial monitored 20-GiB worker/12-GiB reserve
after fresh successful dynamic preflights; independent complete source review.
Revise if an original factor/support guard is lost or a mass/noise inverse
appears. Do not treat a divergent fixed-nome score cap as scaling control.
No new assumption structure, canonical field change or physical closure.

### Squared-residual producer and original centered-correction screen

2026-10-08 UTC. BOTH focused final targets PASS. The generic producer and
literal original-density/OWN-padded-square instances are kernel-checked,
with independent COMPLETE frozen-source review and final-repair refreshes.

Actual generic declarations:

- `centeredRelativeCoefficient_certificate`,
  `lean/YMGap/Continuum/SU2QuaternionConditionalGrussSquare.lean:201`,
  constructs the nonnegative coefficient from the TWO actual signed tilts.
- `residual_square_pin`, same file `:228`, proves `I(W*X^2)=A*nu`.
- `squaredResidualVariance_certificate`, same file `:268`, produces
  `det_W(X^2)<=4*C^2*A^4*nu-A^2*nu^2` from the actual source square cap.

These are Type-valued polynomial Haar certificates, not assumed pointwise
variance bounds. Cap zero, conditional mass zero, zero heads/tail and signed
sources remain allowed. No conditional mass, source, noise or cap inverse is
introduced. The pre-existing Gruss calculation inverts only its explicitly
positive auxiliary `L`.

`original_ratioNoise_densityCovariance_certificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:695`,
retains W=Kkin*S*a and dtilt=Kkin*J(S*a).
It first constructs D0=I(dtilt); the passage D0 -> JA is ONLY supported
Haar-carrier equality, with arbitrary surviving insertions retained. Its
CHECKED output, writing Q=`ratioNoiseDensityMoment`, is

    A^2*(Q-nu*JA)^2
      <= (L^2*A^2-(JA)^2)*(4*C^2*A^4*nu-A^2*nu^2).

The exact full terminal history, spatial and kinetic factors, strict nome,
active physical-link and `endpointRelativeCutoff` guards remain. Terminal
depth zero and i=j are included by the generic original-source statement.
`ownPaddedSquareRatio_densityCovariance_certificate`, same file `:867`,
constructs the literal OWN-padded-square instance with C=17 from
`ownPaddedSquareRatio_squareCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:368`;
its inherited depth/width guards are not removed. Incoming approximation
degree is arbitrary and is not identified with an outgoing reciprocal degree.

The OWN source really matches the backward consumer:
`BF4WilsonAllNomeWindowSignedCost.lean:188` defines its original section,
and `original_window_budget_macro_ratio`, same file `:245`, consumes the
actual dyadic-unit original cost and variance. The finite schedule and OWN
center are literal at
`BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:74`; `mean_pin`,
`BF4ExactSlabFixedSpatialWilsonMeanRadial.lean:104`, identifies the computed
center with that SAME middle ratio. This is not an identification with the
different signed spatial-plaquette span. At fixed nome the existing schedule
K=headCutoff(w)+stage eventually satisfies the additional local cutoff;
this read-only arithmetic observation is not a new Lean onset declaration
or a changing-family estimate.

Independent read-only centering screen (PAPER consequence of the actual
statement, not a new Lean theorem): in
`original_ratioNoise_ward_unitNoiseGradient_le`,
`BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:515`, put
D=JA, R=Vbar^2*G^2 and Cden=Q-nu*D. Substitution gives EXACTLY

    H[R*nu*A*J^2(A)]
      <= H[Vbar^2*matchedNoise(a,Jphi)]
         - H[R*D*Cden] - 2*H[spatial].

The mean square cancels between the original Ward left side and density
correction. It is NOT an additional reserve and must not be counted twice.
The new covariance control supplies neither a sign for D*Cden nor payment
of the spatial correction. Its retained determinant terms cannot be called
a bound on the complete original signed-window cost.

The explicit nome cap is still `endpointRelativeCap`:
`BF4ExactSlabFixedSpatialEndpointRelativeBound.lean:59`. Its already-proved
`endpointRelativeCap_formula`,
`BF4ExactSlabFixedSpatialEndpointTailCalibrationObstruction.lean:42`, pins
L=24608*JacobiShiftedRelativeSlope.budget(w)+7. This allowance is not a
small changing-family payment. Continue JOINT control of signed density,
spatial and conditional-gradient contributions, relative to OWN surviving
variance and BOTH masses; no per-term absolute-bound branch is required.
Complete family payment, continuum survival, physical calibration, full QFT,
every compact simple group and Clay remain OPEN. Canonical chart unchanged.

Observed verification: generic check 3 PASS; Ward check 2 PASS. The earlier
generic failures required namespace opens and an explicit rewrite target;
Ward check 1 required opening the EXISTING `kineticWeight_supported`
(`BF4ExactSlabFixedSpatialKineticHeat.lean:193`). No mathematical statement,
public type, support/cutoff guard or analytic premise changed in the repairs.
Error-induced `sorryAx` output in failed elaborations is NOT accepted as a
gate. All TWENTY final printed gates (5 generic, 15 Ward) are exactly
{propext, Quot.sound}; no error, warning or sorryAx in either final log.
Root reviewed the changed argument and exact original-law pins; independent
COMPLETE reviews covered all 399 generic/998 Ward lines across the frozen
review plus namespace-only final-hash refreshes.

    generic source d212645070908da508a69b0f0343b3f32813b9346ef0ed96d8a77721abc07c8f
    /private/tmp/ym-oct8-squared-residual-gruss3.log PASS
    SHA256 d7bcbc58e90da0e47faea0ea9593991e31cb669ad88a6f8b40a7eac81363a3e6
    Ward source 7d3ac527ffbae9c8f2c07c8c7b5c17df2601d6152ec57b92860e1c43fae60e81
    /private/tmp/ym-oct8-density-covariance-ward2.log PASS
    SHA256 e15f47c9e640603ecf2275c4f314add80685a2c63ba0b56f69f52d0e15d2c1cc

Fresh successful conflict/memory preflight before EVERY launch, one serial
20-GiB worker/12-GiB reserve; observed preflights 81--85% free, zero swap.
Final process handles are terminal. No root/tree build/audit, limit increase,
lock bypass, foreign code, new module/frontier or new analytic premise.
Existing public APIs and user-owned duplicate files remain unchanged.
No canonical atom or physical/scaling/Clay claim is closed; no chart reprint.

## Selected joint gradient/spatial determinant experiment (2026-10-08 UTC)

Selection after commit `32a04a0a`: the direct aggregate screen recovers the
already-open ORIGINAL macro retention target, rather than a new producer.
Reweighting W by Vbar^2 cancels its derivative in centered density covariance,
so it does not absorb the spatial correction. A hemisphere upper heat band
has no unconditional original-law consumer. None is selected for implementation.

The selected finite estimate uses the UNCHANGED conditional law
W=Kkin*S*a, with I=partialHaarHeads, A=I(W), nu=det_W(phi),
t=J_in(phi), D=J_out(A), V=Vbar, e=J_out(V), and
M=A*I(W*phi*t)-I(W*phi)*I(W*t). Every outgoing coefficient is lifted into
the incoming variables. Define the auxiliary test psi=V*t+e*phi, not a
replacement physical observable. Polarization gives exactly

    det_W((V*D+A*e)*phi+A*V*t)
      = V^2*D^2*nu + 2*A*V^2*D*M + 2*A*V*e*D*nu
        + A^2*det_W(psi).

The existing `SU2QuaternionMultiHeadVarianceReplica.determinant_certificate`
constructs its positivity directly; no cancellation or inverse of A is needed.
Together with private `original_ratioNoise_ward_signed_le` and the original
matched moment pins in `BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean`,
the predicted SAME-source consumer is

    H[V^2*G^2*nu*A*J^2(A)]
      <= H[G^2*A^2*det_W(psi)] - H[V^2*G^2*D*(Q-nu*D)].

The existing reciprocal multiplier-square certificate can remove G^2*A^2
ONLY from the positive joint-variance payment. This retains the signed mixed
moment and needs no separate cap on J(V). Zero conditional mass/noise/V/e,
signed phi, depth zero and i=j are decisive degeneracy checks; incoming and
outgoing approximation degrees remain independent. The law, original action,
terminal history and cutoff guards may not be changed.

Budget: bounded additions to the existing generic determinant and original
Ward leaves; ROOT alone runs two serialized focused checks, each after fresh
successful live conflict/memory preflight, one 20-GiB worker/12-GiB reserve.
Independent full final-source review; no root/tree build or new interface.
Abandon or revise if the actual moments do not match, if a source/mass inverse
is required, or if a new spatial-derivative cap is supplied as a premise.

This is NOT uniformly stronger after discarding the determinant reserve:
its comparison with the old spatial payment has no produced sign. Its value
is retaining cancellation inside the ACTUAL joint conditional variance.
A useful moving-family bound of joint variance AND centered density payment
against OWN surviving variance and BOTH masses is still open. No canonical
proof status, physical statement, or Clay conclusion changes by selection.

### Observed result and continuation decision

Both final focused checks PASS. Generic `residual_mixed_pin`,
`determinant_lifted_combination_pin`, `jointGradientAbsorption_certificate`
are at `lean/YMGap/Continuum/SU2QuaternionConditionalGrussSquare.lean:419`,
`:492`, `:532`. The certificate is constructed from det_W(z), not supplied
as a variance input; all outgoing coefficients are explicitly lifted.

The original instances are `ratioNoiseJointGradientVariance`,
`original_ratioNoise_jointGradient_certificate`,
`original_ratioNoise_ward_unitJointGradient_le`, at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:987`,
`:999`, `:1076`. The FINAL checked consumer is the predicted estimate after
removing the outgoing reciprocal from ONLY its positive payment:

    H[V^2*G^2*nu*A*J^2(A)]
      <= H[det_W(V*Jphi+(J V)*phi)]
         - H[V^2*G^2*(JA)*(Q-nu*JA)].

It sums G^2 times the produced joint certificate with the ACTUAL positive
joint-noise certificate times the existing multiplier-square certificate.
No separate J(V) cap, density-correction sign, inverse conditional mass,
source substitution or incoming/outgoing degree identification appears.
The exact same mean-derivative square cancels ONCE between the left-side
Fisher term and the density center; no extra reserve is counted.
The generic certificate admits zero W, conditional mass/noise, V or e,
signed tests and zero head/tail extents. The original consumer preserves
strict nome, headCutoff, supported test, selected-plane guards, depth zero,
i=j and arbitrary successor reciprocal degree. No new analytic premise.

Observed compiler repairs were ONLY multiline match-layout changes: generic
check 1 failed in two polynomial valuation matches; Ward check 1 failed in
one scalar valuation match, and the other two new multiline scalar matches
were formatted consistently. ROOT caught nested coefficient/congruence
associations before the first Ward launch. None changed the mathematical
formula, hypothesis, old public API or actual law. Failed elaborations'
error-induced sorryAx output is NOT an accepted axiom check.
Generic check 2 and Ward check 2 have no error, warning, sorryAx or classical
dependency; all TWENTY-SIX printed gates are exactly {propext, Quot.sound}.

    generic source d44d58fd035b1f9ad4fb4942babd1e3055fe9697aaa2e1f58e6d6078ee231cda
    /private/tmp/ym-oct8-joint-gradient-gruss2.log PASS
    SHA256 f55600e109e58d2dd2947984a683e2cf948e3f9925e0015d0db4a278ef4ee9e5
    Ward source e0a411ef9da50fed6aff952e79b9d22be1080375c3a4187e20b8089c023b9409
    /private/tmp/ym-oct8-joint-gradient-ward2.log PASS
    SHA256 98ed0e6c6434709b7671a839f4d80ffc8539ab982b82bb389470440e11ac9a96

ROOT inspected the argument and original-law pins. Independent COMPLETE
source review covered all 597 initial generic and 1247 initial Ward lines,
then every local repair and final frozen hashes (607/1254 lines). A further
parallel paper screen confirmed methodological relevance, not a foreign
theorem import or Wilson-source Taylor zero. Fresh successful conflict and
dynamic-memory preflights before EVERY launch; one serial 20-GiB worker,
12-GiB reserve, observed 82--85% free and zero swap. All process handles
are terminal. No root/tree build/audit, limit increase, new module/frontier,
foreign code or touched user-owned duplicate file.

CONTINUE the useful joint estimate: det_W(psi) together with the signed
centered density correction versus OWN surviving variance and BOTH masses.
No sign makes this automatically stronger than the previous separated bound;
the opportunity is cancellation inside the actual joint conditional variance.
This reduces the form of the finite payment, not its changing-family size.
Continuum survival, physical mass calibration, full same-theory QFT, every
compact simple group and Clay remain OPEN. Canonical chart unchanged.

## Selected direct-retention versus window-budget kernel screen (2026-10-08)

Previous turn: PROGRESS as a documentation-only selection refinement,
commit `2c10553f`; no new analytic theorem. The two bounded mathematical
screens now return to already-known missing inputs, so neither a normalized
telescope wrapper nor a generic adaptive-order interface is selected.

The exact finite telescope on paper is
`2*c_t=v_t-v_(t+1)+ell((W_t*b_t-Z_t*T*b_t)^2)/(Z_t*W_t^2)
 -(Z_t*Z_(t+1)-W_t^2)*v_(t+1)/W_t^2`.
It retains the distinct masses. Its completed remainder is the nonnegative
second defect, not an unpaid favorable reserve. This is PAPER, not a new
Lean identity; the earlier audit already distinguishes direct retention
from the sufficient window budget.

Select a bounded kernel certificate for a concrete instance of that earlier
two-mode screen in `computations/window_reserve_two_mode_screen.py`:
`u=8`, `lambda=1/100`, `mu=31/32`,
`R(n)=lambda^(2*u)*mu^n+mu^(2*u)*lambda^n`. Return the horizon and retention
coefficient as explicit data; prove positive warmed response, rates in
`(0,1)`, `R(4*u)>=R(2*u)/4`, and failure of
`2*sum_{t=u}^{2*u-1}(R(2*t)-R(2*t+1))<=R(2*u)`.
Prediction: exact rational inequalities pass by kernel computation.
Degeneracy check: positive warmed response and both strictly nonstationary
modes exclude zero-state/vacuum artifacts. This is NOT an original YM state.

Consumer of the route-selection evidence is the choice between actual
original macro retention and `WindowSignedCost.original_window_budget_macro_ratio`'s
stronger sufficient input. The latter remains eligible, not mandatory.
No canonical field changes. Budget: a short addition to the EXISTING
`RationalMacroRetentionWithoutInitialEnergy` leaf; one focused monitored
20-GiB/one-worker check with 12-GiB reserve after a fresh capacity/conflict
preflight, plus independent final-source review. No root/tree audit.
Abandon expansion if this requires a new frontier/interface, foreign oracle,
or any claim that the toy moments estimate the original interacting source.

### Observed finite separation and next decision

Focused check1 PASS, exit0. All NINE new public gates are AXIOM-FREE; all
TEN existing gates remain within {propext, Quot.sound}. No errors, warnings,
sorryAx, choice, native computation or option increase. ROOT inspected the
complete final248-line source; independent COMPLETE frozen-source review
PASS with the matching hash. The exact eight losses at 16,18,...,30 match
`aggregate_window_macro_ratio`'s u=8 criterion. Rate positivity/strictness
and R(16)>0 exclude a zero-norm or vacuum counterexample.

The new declarations are `windowSeparation_retention:204`,
`windowSeparation_budget_fails:209`, `windowBudgetSeparation:216` in
`lean/YMGap/Continuum/RationalMacroRetentionWithoutInitialEnergy.lean`.
The witness returns u=8 and kappa=1/4, without erasing them into Exists.
Failure at kappa=0 also excludes the stronger quarter-margin window test.
The all-horizon PAPER argument and the actual BF4 source estimate are NOT
claimed checked by this one finite witness.

    final source 7e7f391d4ada65b3ced4d652049b5589aea80178ef7ca06813c534f4b76a0be5
    /private/tmp/ym-oct8-window-separation1.log PASS
    SHA256 e98f94f9d409308a5b3a737e834d34b4c0fa854a6bcbf77b9f44d06d079be63f

Fresh conflict/memory preflight: no competing compiler/runner/test process,
84% system-wide free memory, zero swap observed before launch. One serialized
20-GiB monitored worker with 12-GiB reserve; handle73286 is terminal.
No root/tree build/audit, limit increase, lock bypass or touched duplicate.

CONTINUE DIRECT original macro moments as a co-primary analytic producer,
alongside sufficient joint signed cost. In particular
`normalizedAnchorResponse_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`,
consumes the direct SAME-source ratio, not the stronger residual sum.
No reverse macro-to-window implication or unnecessary initial-norm floor
is required. No new interface/frontier or canonical field is introduced.
The actual interacting ratio/relative payment, justified scaling, continuum
survival, physical calibration, full QFT, every group and Clay remain OPEN.
Displayed chart claims unchanged; no chart reprint.

## Direct-moment selection and a rejected hemisphere adaptation (2026-10-08 21:23 UTC)

Previous goal turn: PROGRESS, `90b15148`, a checked finite separation of
sufficient criteria plus its planning correction, NOT an interacting estimate.
Two independent read-only source screens found no new useful original
changing-family moment producer. No compiler or numerical sweep was launched.

The next DIRECT test is the actual macroscopic ratio, not an obligatory
near-unit MICROSCOPIC ratio. With s=side(scale), let J_L/Z_L denote
`centeredPair` with the SAME finite OWN center and the literal lag-L
partition. Test the complete signed numerator

    Z_s*J_(2s) - kappa*Z_(2s)*J_s >= 0.

The quantities are those of `centeredPair`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMovingCenterLagDifference.lean:57`;
the fixed-member limit join is `expressionOwn_centeredPair_converges`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.lean:251`.
The completed consumer is `normalizedAnchorResponse_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`.
All sources, actions and chronological partitions stay unchanged. Microscopic
ratio propagation remains a sufficient alternative when its useful rate AND
original overlap are produced; small Hankel spread alone supplies neither.
Neither a common depth across the scaling family nor a raw-norm floor is
an extra prerequisite for removing the fixed-member approximation.

The original plaquette FAMILY already has a produced `family_rayleigh_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:104`;
it must not be described as absent or substituted for the dyadic LOOP's
changing-family reserve. Its spectator fraction is not a near-unit rate.
The literal loop's `paddedSquare_connected_overlap_cleared`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareConnectedDualOverlap.lean:230`,
still needs a useful actual overlap magnitude. Fixed-source reproduction by
`conditionalHeat_one_endpoint`,
`lean/YMGap/Continuum/SU2QuaternionConditionalHeatEndpoint.lean:140`,
does not bound the complete moving original source or both partitions.

### A short PAPER estimate, not a selected Lean implementation

For 0<w<1, 0<=x<=1 and the EXISTING endpoint tail onset, put
C=nearFlatCap(w), M=M1(w,x,N), V=M2(w,x,N), P=normalizedProduct(w,x,N).
The literal `sTerm` denominator increases with x, so M>=M1(w,1,N).
`endpoint_firstMoment_payment`,
`lean/YMGap/Continuum/JacobiProductRadialNearFlatBound.lean:504`, gives
M>=C-13/4; `secondMoment_le_first`,
`lean/YMGap/Continuum/JacobiHeatNearFlatLogHessian.lean:103`, gives V<=M.
Using the ACTUAL heat pins `heat_eval_moment_pin` and
`heat_first_moment_pin`,
`lean/YMGap/Continuum/JacobiHeatRadialMomentJets.lean:214` and `:226`,

    h'-(C-17/4)*h ≈ P*(M*(M-(C-13/4))+(M-V)) >= 0,
    C*h-x*h' <= ((1-x)*C+x*(17/4))*h.

This sharpens the earlier PAPER band and requires no heat inverse,
assumed heat positivity, or N>=2. P and M are produced nonnegative;
N=0/1 remain governed by the actual tail guard. `sTerm` is at
`lean/YMGap/Continuum/HeatKernelConv.lean:224`; computed onset/tail are at
`lean/YMGap/Continuum/JacobiProductRadialNearFlatBound.lean:685`, `:687`.
ROOT's algebra and an independent mathematical/source review agree.
This composition has NOT been added to Lean or kernel-checked as a new theorem.

REJECT implementation for MAIN now: a certified original-law hemisphere
noise/source-weighted restriction/complement payment against surviving OWN
variance is NOT FOUND in the inspected
`SU2QuaternionPairedFrozenHeatPrefixCurvature` and
`BF4ExactSlabFixedSpatialTerminalLocalSignedGram` modules. Their current
global deficit transport and `terminal_local_signed_score_bound_nearFlat`,
the latter at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalLocalSignedGram.lean:799`,
do not consume this hemisphere-only upper contribution or pay the signed
action/spatial score covariance. No localization premise is introduced.
Continue the complete ORIGINAL macroscopic numerator or JOINT signed payment;
no new interface, proof-node closure or chart-state change is claimed.

Source-inventory correction, 2026-10-08: ORIGINAL edge-MASS localization
already exists in `exact_alignment_normalized_of_cutoff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialExactKineticAlignment.lean:95`,
at its computed nome-dependent cutoff. It does not cover the squared
conditional residual or pay the above MAIN variance budget. No duplicate
alignment proof is selected. Exact source chain and prior verification
boundary: the final section of `RESEARCH-2610-09093-2026-10-08.md`.

## Trace-sign experiment and warmed-budget screen (2026-10-08 UTC)

Previous goal turn: PROGRESS, `5164c1e2`, a source/PAPER selection correction,
not a new interacting estimate. Two independent read-only mathematical
investigations now test the next proposed joins, without a numerical sweep.

Experiment: determine whether positivity, simultaneous kinetic angular
invariance, OWN centering and the complete Haar/plane trace force a sign for
the centered density payment retained by
`original_ratioNoise_ward_unitJointGradient_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:1076`.
The existing finite Haar regression leaf is the intended certificate location;
it is not an original BF4 action instance or a physical observable replacement.

PAPER prediction, independently derived: on two unit quaternions let
K(x,y)=1+(x dot y)/2, g(x)=1+7*x0/8, W=K*g. The actual density has floor
1/16, and K is invariant under each simultaneous coordinate-plane rotation.
With I=integrate the incoming quaternion, A=I(W), B=I(W*phi),
nu=A*I(W*phi^2)-B^2, X=A*phi-B and
Q=I(K*(J_in g)*X^2), use the actual outgoing D=J_out A. At V=1 and
the literal upper-window-2 reciprocal of degree one, G=1/2. The complete
six-plane outer-Haar sum of G^2*D*(Q-nu*D) is predicted to be

    phi=x0-7/32:   +61103/1610612736,
    phi=x0^2-1/4: -298655/6442450944.

Both tests are OWN-centered in the SAME globally normalized W law. Opposite
signs would reject this universal sign argument, not interacting Yang--Mills
survival or a sign theorem using additional actual action structure.
The quadratic test has a short PAPER factorization: with q=t*r and xi=q*y0,
`Q-nu*D = D*((xi-4)*(xi+1)/192)`. Its bracket is strictly negative for
|xi|<1. This sign is not a conditional Gram failure; the density is positive
and its variance determinant remains nonnegative.
Verification budget: one focused serialized 20-GiB Lean worker with 12-GiB
OS reserve after fresh process/dynamic-memory checks, and independent complete
final-source review. No root/tree audit, foreign code, new premise or axiom.
Abandon implementation if it requires a generic analytic interface rather
than a small exact finite certificate. Observed verification belongs below;
the rational predictions above are PAPER until checked. The stronger second
test replaced an earlier non-class coordinate test. BOTH final tests are
polynomials in the conjugation-invariant scalar x0; no full local gauge or
original-action identification is asserted.

Independent DIRECT-route screen (source/PAPER): write R_n=B(x,T^n x),
delta_n=R_n-R_(n+1), D_s=R_s-R_(2s), s>=1. Monotonicity gives
D_s<=s*delta_s. The existing `mixedMoment_column_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:91`, gives
D_s<=s*R_0/(s+1). Paying this particular ceiling in R_s units would require
R_0<=(1-kappa)*(s+1)*R_s/s. For R_s>0 and kappa>1/(s+1), this is incompatible
with R_0>=R_s. It refutes the sufficiency of that absolute ceiling for a
fixed positive large-s retention fraction, NOT the actual retention claim.
The positive last term in `mixedMoment_time_budget`, same file `:71`, instead
gives s*delta_s+R_s<=R_0 and hence R_(2s)>=2*R_s-R_0; its useful join still
needs the unproduced floor R_s>=R_0/(2-kappa) when 0<kappa<1.

`conditionalHeat_weighted_angular_variance`,
`lean/YMGap/Continuum/SU2QuaternionConditionalAngularPoincare.lean:132`,
pays conditional variance by (1-w^2) times the INPUT gradient. It cannot
erase the actual spatial derivative in T f=P(V f):
`transferStep_kineticMap`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticContraction.lean:72`,
and `productMap_angular_carrier`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularCommutation.lean:59`,
give J(Tf)=P(V*Jf)+P((JV)*f) under their support/angle guards.
The complete ratio derivative additionally retains its signed density-score
covariance. Reject another warming/Poincare propagation wrapper without
payment against the actual warmed OWN variance. Direct macro retention and
quantitative action-dependent joint payment remain co-primary OPEN targets.

Observed finite verification, 2026-10-08 UTC: focused check3 PASS; the
existing leaf is already imported by `lean/YMGap.lean:7337`, and no root
registration or root/full-tree build was needed. The following declarations
are now kernel-checked in
`lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.lean`,
namespace `QuaternionHaarConditionalRegressionWitness.ScoreSign`:

- `source_mass_and_centering`:212, `moments_are_actual`:220 and
  `score_inputs_are_actual`:236 pin the actual law, OWN centers and inputs.
- `boundary_density`:251 and `reciprocal_one`:257 pin A and literal G.
- `coupling_pair_invariant`:263 proves invariance on the actual two-head
  Haar carrier, including arbitrary polynomial insertion, NOT raw exponent
  list equality. It composes the existing
  `scalarAt_pairedAngular_carrier_at`,
  `lean/YMGap/Continuum/SU2QuaternionRelativeHeatAngularInvariant.lean:189`.
- `dot_certificate`:288, `coupling_floor_certificate`:297,
  `incoming_floor_certificate`:304 and `source_floor_certificate`:314
  return Type-valued positivity certificates, including W>=1/16.
- `total_phi0_exact`:327 and `total_phi1_exact`:332 prove the two opposite
  fractions above; `bare_totals_exact`:336 retains the same signs without
  G^2. `score_signs`:341 proves both strict inequalities directly.

Every one of the fourteen new public axiom prints, and every pre-existing
print in this focused leaf, is empty or contained in {propext, Quot.sound}.
No literal `sorry`, new axiom, classical shortcut, trusted external
calculation or weakened original-action obligation is introduced.

Verification command, from the repository root:

    python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.olean --log-file /private/tmp/ym-oct8-trace-sign3.log

Checks1/2 terminal FAILED before repair. Check1 found an unavailable
`interval_cases` tactic and unpinned coordinate arguments. Check2 found
that paired angular cancellation is false as arbitrary raw coefficient
probe equality: differentiation preserves unequal trailing-zero list
lengths. The final repair uses the already proved supported Haar-carrier
cancellation, as explicitly documented in
`derivative_self_carrier`,
`lean/YMGap/Continuum/SU2QuaternionAngularCoordinate.lean:46`.
Elaboration-generated `sorryAx` in those failed logs was rejected; it is
absent from every final gate. No failed result is counted as a proof.
An independent complete final-source reviewer PASSed the exact frozen
final hash below after the correction. Both exact fractions were also
derived independently before compilation.

SHA256 evidence:

    final Lean source: ef041d8fe04172dd88706f3b2b6c8ac1e539b1fcaac289363c1dc5d7ba05dd6f
    /private/tmp/ym-oct8-trace-sign1.log: f938ddc2f55cc6785707e8750d74b94711f163c16814549ce5dbdd1ad6f0cc77
    /private/tmp/ym-oct8-trace-sign2.log: 9ddcc37410b2d7309471c5be89266aa8f1739ae1faf2e03df4ae764d71578fb6
    /private/tmp/ym-oct8-trace-sign3.log: 4d653f6d6cf8b8ffab0bbbb13bbcb90dd4f3ccdec6ca2eb86081128f3842da11

Each launch followed a fresh successful live process/memory preflight;
the last reported 83% memory free and zero swap, with no competing worker.
Checks used one monitored 20-GiB worker, 64-MiB stack and 12-GiB OS reserve.
The auxiliary namespace's finite-normalization settings (maxRecDepth=100000,
maxHeartbeats=12000000) match the imported differential leaf; these are
not raised worker/OS-memory limits. No broad build or audit was run.

Conclusion: positivity, paired kinetic-coupling symmetry, OWN centering and complete trace
do NOT determine a universal sign for this correction. A sign conclusion
using extra actual action/source structure is not refuted. The original
JOINT signed estimate versus surviving OWN variance, or DIRECT original
macro ratio, remains OPEN. No canonical displayed proof claim changes.

## Selected test: PSD alignment residual versus signed energy (2026-10-08)

Previous goal turn: PROGRESS, `0ecdeb93`, a corrected original-input inventory
and rejection of duplicate alignment work, not a new physical estimate.
Current independent forward/backward reviews found a decisive algebraic
test before using that input on the MAIN energy difference.

For a bilinear kernel form B write E_B(a,f)=B(a,a*f^2)-B(a*f,a*f).
With R_i=B_{K*(X_i-w^3)}, the actual alignment input is PSD of R_i.
The proposed join would need a favorable sign or quantitative payment of

    R_i(a,a*f^2) - R_i(a*f,a*f).

PSD of R_i alone does not sign its mixed first term. The selected diagnostic
uses the ACTUAL one-link SU(2) heat prefix at w=1/2, cutoff1, a=1 and f=x0.
PAPER prediction: R_i(1,1)=R_i(1,f^2)=0,
R_i(f,f)=15/256, so its energy remainder is -15/256, although R_i is PSD.
The original heat is strictly positive and f is centered in its OWN law.
This is a finite heat-kernel algebra screen, NOT a BF4 action, its closed
Wilson algebra, a surviving excitation or a Yang--Mills counterexample.

Existing MAIN consumers: `energy_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:267`, retains
the full original jump square; `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`, demands the
complete signed cost relative to OWN surviving variance. The DIRECT alternative
`normalizedAnchorResponse_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`,
still demands its original macroscopic ratio and BOTH chronological masses.
The test removes no original obligation; it screens an invalid universal join.

Available inputs: actual `heatAt`, character insertion positivity and the
existing finite Haar witness leaf. Plan one bounded addition in that EXISTING
leaf, no new interface or canonical field. Independently review final source,
then use one serialized monitored 20-GiB worker and 12-GiB OS reserve after a
fresh dynamic preflight. No root/tree check or limit increase. Revise/abandon
if the claimed PSD cannot be pinned to the actual residual or if the finite
moments differ; no substitute kernel is permitted. Observed verification and
the resulting continue/revise/prune decision will be recorded separately.

### Observed: kernel PSD does not sign the energy remainder

Focused check2 PASS, 2026-10-08 UTC. The EXISTING
`lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.lean`,
namespace `AlignmentEnergy`, now proves:

- `heat_kernel_pin`:398 and `heat_floor_certificate`:414 pin the literal
  cutoff-one heat and its positive half-floor on two quaternion Haar heads.
- `residual_character_pin`:407 identifies
  R=(15/32)*chi_1+(1/8)*chi_2; `residual_quadratic_nonnegative`:421 proves
  its supported PSD quadratic for EVERY signed one-head polynomial, using
  the existing actual character Gram and the unit remaining kernel.
- `f_supported`:456 and `own_source_moments`:472 retain the actual supported
  coordinate, original heat mass1, OWN mean0 and variance1/4.
- `residual_entries`:479 proves R(1,1)=R(1,f^2)=0 and R(f,f)=15/256.
  `energy_remainder_exact`:485 proves the mixed-minus-diagonal remainder
  equals -15/256 and is strictly negative.

R is a sign-changing kernel insertion, NOT a positive probability density.
Its PSD operator form is insufficient to make its Dirichlet energy positive;
the actual positive K energy is not refuted. This screens the proposed
universal kernel-order-to-energy-order inference, NOT the original BF4
action/closed Wilson algebra, DIRECT retention or the Clay problem.

All 21 new printed gates and 32 previous gates are empty or contained in
{propext, Quot.sound}. No literal `sorry`, new axiom, `Classical.*`,
`native_decide`, canonical-field change or trusted external computation.
Independent COMPLETE frozen 514-line final-source review PASS.
Check1 terminal FAILED on missing `SupportedQuaternionBlocks`/`supported_one`
namespace opens; the defining declarations were located and opened before
check2. Elaboration-generated `sorryAx` in that failed log was rejected;
every final printed gate is permitted. No mathematical statement was weakened.

Accepted verification command, repository root:

    python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.olean --log-file /private/tmp/ym-oct8-alignment-energy2.log

SHA256 evidence:

    final Lean source: 5fc022ddb6d97ee6396e389a8df12d878154f5338a10d741fc0b79ff694f0ab9
    /private/tmp/ym-oct8-alignment-energy1.log: 2bb2e960fa200c45b6d74d5ab6ec9abf52686f776259c356d62045564857af78
    /private/tmp/ym-oct8-alignment-energy2.log: 3d0fbb60710737cdd3c1b0bdd3b9329c90771763c9ec4bd1e6723e61f29561f4

Each launch followed a fresh successful live process/memory preflight:
83% memory free, zero swap and no competing compiler/runner/pytest process.
One monitored 20-GiB worker, 64-MiB stack and 12-GiB OS reserve; no root/tree
build/audit or resource-limit increase. Local finite-normalization settings
match the imported differential leaf and previous score-sign namespace.

The parallel ORIGINAL Casimir screen is source analysis, not a new theorem.
`family_ward`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:124`,
already gives marginalAngular+wardResidual=12*oddMass*oddVariance using
`spatialSpan_casimir`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCasimir.lean:294`.
The residual defined by `blockResidual` and `totalResidual`,
`lean/YMGap/Continuum/SU2QuaternionWeightedCasimirWard.lean:45`, `:59`,
retains J(spatialWeight*g_n*g_(n+1)) against (f-c)*Jf.
The current joint Ward payment instead uses the pullback Sa*T(Vbar*A), by
`original_ratioNoise_noiseGradientPayment_weighted_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:631`.
Bare Casimir eigenpins do not identify these weights or eliminate the full
source/fringe correction and negative predictable-gradient square.

**Decision:** PRUNE the PSD-to-favorable-energy shortcut and duplicate
Casimir cancellation work. CONTINUE a quantitative action-dependent complete
signed estimate in warmed OWN-variance units or the actual macroscopic
numerator, preserving BOTH chronological partitions. No new analytic premise
or original relative budget is supplied by this diagnostic. Scaling survival,
physical calibration, full QFT/every-group/Clay remain OPEN. No canonical
displayed proof/expansion state changed; no ASCII reprint.

## Direct dual selection: original symmetry-sector contraction (2026-10-08)

Selection recorded 22:34 UTC, BEFORE implementation. The previous goal turn
made a source/planning refinement, not a Yang--Mills estimate. Two read-only
reviewers now confirm that the finite macro detector algebra is already
available: `normalized_block_window_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:140`, plus
`weighted_cauchySchwarz`,
`lean/YMGap/Continuum/QuaternionHaarWeightedCauchySchwarz.lean:87`, and the
actual `spatialCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialOrder.lean:129`.
The existing moving-OWN-center limit and direct completed macro consumer
remain; do not implement a duplicate macro pin.

**Next proposition:** on the EXISTING original Wilson completion, construct
`P_plus(v)=(v+U v)/2` and `P_minus(v)=(v-U v)/2`, where U is the already
constructed literal spatial-axis swap. Prove the exact norm split,
norm contraction, original-time commutation and preservation of a detector
against a source in the corresponding ACTUAL symmetry sector. These are
new quantitative test improvements, not a claimed relative overlap floor.
For a source without a proved sector pin, do not project it or assume one.

Available inputs: `completedSwap_involutive`, `completedInner_swap`,
`completedInner_swap_balance` and `completedSwap_time`,
`lean/YMGap/Continuum/BF4WilsonAllNomeSpatialAxisSwapCompletion.lean:61`,
`:125`, `:131`, `:70`; literal completed linearity and form positivity.
Actual consumer: the original macro dual Cauchy--Schwarz test can retain
its detector with a no-larger dual denominator after this projection.
It does not produce that detector, a uniform useful overlap or a scaling
trajectory. No new carrier, measure, analytic hypothesis or frontier bundle.

**Prediction/test:** orthogonal plus/minus sectors, including zero tests,
give exact Pythagorean splitting; common warming cannot create a cross-sector
detector. The produced antisymmetric two-plaquette source is an action-specific
test candidate, with an already checked positive initial norm, not MAIN's
padded square or a proved slow mode. An unqualified nonzero-different-dual
inference must be rejected. Implement the short projection algebra in
the existing swap leaf and its ACTUAL odd-sector source instance in the
existing `BF4WilsonAllNomeAntisymmetricPlaquette.lean` leaf. ROOT owns that
second leaf; Sol owns only the swap leaf. Check these two focused targets
serially. Abandon if either needs an unproduced analytic premise
or duplicates an existing projector. MAIN still needs an actual quantitative
same-sector overlap or JOINT signed payment.

**Verification budget:** Sol bounded implementation and independent read-only
review; ROOT only serial focused checks after fresh dynamic-capacity checks,
one 20-GiB worker with 12-GiB OS reserve. No root/tree build or audit, no
resource-limit increase. No new `sorry`, axiom, canonical field or chart state.
Observed verification and final source hashes will be recorded after the test.

### Observed original-sector result and verification

2026-10-08 22:40 UTC. Both first focused serial checks PASSED, without proof
repairs. These are new kernel-checked algebraic/actual-source results, not
the missing original relative estimate:

- `evenPart`, `oddPart`, `sector_norm_split`, `evenPart_norm_le`,
  `oddPart_norm_le`, `evenPart_time`, `oddPart_time`, `evenPart_detector`,
  `oddPart_detector`, `oddPart_vacuumComplement`,
  `evenPart_preserves_vacuumComplement`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeSpatialAxisSwapCompletion.lean:161`,
  `:164`, `:234`, `:260`, `:268`, `:276`, `:281`, `:287`, `:296`, `:307`,
  `:325`. Norm splitting is exact on the SAME completed pairing. The
  detector identities require literal matching source-sector pins.
- `excitation_swap_odd`, `excitation_time_swap_odd`,
  `excitation_time_oddPart_detector`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeAntisymmetricPlaquette.lean:179`,
  `:215`, `:224`. The unchanged p01-minus-p02 source supplies an ACTUAL
  odd-sector input through the existing two oriented loop-swap equalities.
  Its positive initial norm and exact centering remain the existing results.
  MAIN's padded square has not been substituted or assumed to share this pin.

COMPLETE independent final-source reviews PASS for frozen hashes:

- Swap completion SHA-256
  `a8c38e197fc381b22d2c8c21c8590023b91a91341a38d68345d78a7caa424736`.
- Actual-source leaf SHA-256
  `3dbacebed4a49a50ba821cbd025493e1fab5049798949d2a73d79859047975b0`.

All fourteen new public definitions/theorems print only
`[propext, Quot.sound]`; no new hole, axiom, classical use or analytic premise.
Focused log paths and SHA-256:

- `/private/tmp/ym-oct8-symmetry-sector-check.log`:
  `931ba681a8238578276876d50d0b8af564d5da6ede7a232fb670ed492b9aaf49`.
- `/private/tmp/ym-oct8-antisymmetric-sector-check.log`:
  `ab55d2ee91b0932bda499a85e9a3c1f526a4fe850896fe72bbcaa33e7ee4322b`.

Each used the safe launcher with jobs1/20-GiB hard worker/12-GiB OS reserve,
after a fresh process and capacity preflight. No other build was running;
reported free memory was 84% then 83%, observed swap zero. No long-running
job, root/tree build or broad audit, resource limit increase or foreign-code
execution occurred. No whole-repository verification is inferred.

**Decision/residue:** REUSE the symmetry-matched dual projection for an
actually pinned source; PRUNE tests in the wrong sector and unqualified
inferences from a different nonzero dual. The finite weighted-CS macro join
is already present, so add no duplicate compiler. Produce a useful
action-dependent SAME-sector overlap against the transmitted source, keeping
BOTH chronological masses, or the complete JOINT signed payment versus OWN
variance. These theorems provide neither that overlap nor a positive-time
source norm floor, justified changing family, continuum excitation or physical
gap. Contraction of both norm and macro defect alone does not order their
ratio. Clay/canonical displayed claims remain OPEN/unchanged; no chart reprint.

## Actual odd-excitation transfer test: padding is necessary (2026-10-08)

Selection recorded BEFORE implementation. Previous goal turn: PROGRESS,
the checked SAME-completion sector averages and actual-source pin were
committed/pushed as `8546b8b7`; no survival/scaling/Clay claim was closed.
The active goal and target remain unchanged.

**Next proposition/consumer:** the produced antisymmetric excitation at
width ONE has zero original one-step image despite its strictly positive
initial norm. This screens its use as a DIRECT macro detector source. The
exact two-face kernel instance is NOT already declared. It can be proved
in the EXISTING `BF4WilsonAllNomeFringeTimeKernel.lean` leaf, by cancelling
both equal ORIGINAL centering coefficients and using the two inactive-face
time pins. No new completion, action, analytic input or frontier structure.

Available original inputs: `excitation_norm_floor`, `state_mean_zero` and
`excitation_swap_odd` in `BF4WilsonAllNomeAntisymmetricPlaquette.lean`;
`x_antisymmetric` in `BF4WilsonAllNomeOriginPlaquetteOrbitResponse.lean:241`;
`centeredPart_embed` in `BF4WilsonAllNomeCenteringPin.lean:78`;
actual completed linear/unit-projection laws;
`inactive_face_time_one_zero`, `originFace_not_fully_active` in
`BF4WilsonAllNomeFringeTimeKernel.lean:59`, `:76`, and the literal far02
link index in `BF4ExactSlabWidthOneGeometry.lean:48`.

**Prediction/decisive contrast:** width1 kills BOTH centered faces; width>=2
does NOT. The latter is ALREADY supplied by
`family_time_geometric_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:110`,
with base1, the literal two-face family, rho=`familyResponseFraction(w,2)`.
Do not implement another positive-time propagation compiler. The existing
`familyResponseFraction_le_ceiling`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:64`,
bounds this COMPUTED lower-bound coefficient by 2^(-560); it says nothing
about an upper bound on the true source response. Thus the available padded
positive response does not supply the missing near-unit/scaling rate.

**Budget/abandon condition:** Sol implements only the concrete width-one
instance in that existing fringe leaf; independent complete-source review,
ROOT serial focused safe check20-GiB worker/12-GiB reserve after fresh dynamic
preflight. Abandon if the join needs a new analytic premise, full-tree check
or source substitution. While checking, investigate MAIN's complete original
signed-payment estimate, not further sector interfaces. No new hole, axiom,
canonical field or displayed chart state; record observed result separately.

### Observed concrete transfer screen and narrowed next action

2026-10-08 22:49 UTC. First focused check PASSED. The new public results are
`face02_not_fully_active`, `antisymmetric_excitation_time_one_zero`,
`antisymmetric_excitation_time_positive_zero`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFringeTimeKernel.lean:100`, `:126`,
`:176`. The source is the literal existing antisymmetric excitation at width1,
not a replacement. Its original unit coefficient is zero, so the two
individual ORIGINAL plaquette mean corrections agree and cancel exactly.
Pairing extensionality identifies the raw source with their centered
difference; actual time linearity and the two inactive-face pins kill it.
The original semigroup then kills it at every positive integer time.
Initial norm positivity is unchanged. It is not a Yang--Mills counterexample.

COMPLETE independent 257-line final-source review PASS, SHA-256
`23b3834108445ff66a39b484168811ba1532abdc5edbdc59bb674eaa5f359a6d`.
Focused log `/private/tmp/ym-oct8-odd-fringe-check1.log`, SHA-256
`cbfa2498376050d82eb4ca60731b9b39214d256c88f8affc05b1a3dbc00f26dc`.
All three new public gates and the six retained gates print only
`[propext, Quot.sound]`; no error, new hole, axiom, classical use or premise.
Safe launcher jobs1/20-GiB worker/12-GiB reserve, fresh preflight with no
other build, 83% reported free memory and zero swap. No full-tree audit,
limit increase or foreign-code execution. No whole-library verification.

**Decision:** PRUNE the width1 state as a positive-time detector/non-erasure
witness. REUSE the existing padded family geometric response, not another
compiler: at width>=2, base1 and the literal two-face family supply the
positive lower coefficient rho(w,2), independent of width, regulators and
boundary time. This is source-reviewed reuse of the existing theorem, not a
newly compiled geometric-floor instance here. Its computed rho<=2^(-560)
does not yield a useful scaling rate; no upper bound on the TRUE response
follows from a ceiling on this lower-bound coefficient. The MAIN padded
dyadic square remains unchanged; no arbitrary completed width map is inferred.

The independent MAIN review found the proposed full gradient/spatial
determinant reassembly ALREADY checked, by
`original_ratioNoise_jointGradient_certificate` and
`original_ratioNoise_ward_unitJointGradient_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRatioNoiseWardAbsorption.lean:999`,
`:1076`. It retains the actual negative transmitted-mean square and leaves
exactly the signed centered density correction in the equation recorded in
the earlier joint-gradient section. No unconditional favorable sign or
additional positive-form reduction was found. Do not reimplement that join
or count the matching mean-square reserve twice. CONTINUE the missing
action-specific estimate of joint variance MINUS centered density payment
against OWN surviving variance and BOTH masses, or DIRECT original macro
retention on a justified changing family. Padding, local positive response
and symmetry matching do not replace it. All continuum/physical/QFT/every-
group/Clay and displayed canonical claims remain OPEN/unchanged; no chart.

## Score-controlled original variance floor: selection (2026-10-08 UTC)

Previous goal turn: no new mathematical estimate or authoritative change.
The direct macro-defect identities and consumers were already implemented;
another warming/conditional-innovation wrapper is not selected. A read-only
arbitrary-gap screen retains chronological boundary drift even with an exact
quotient source. Likewise, simultaneous kinetic rotations transfer derivatives
to the actual spatial action and terminal source; the existing Haar Bochner
identity does not delete the density-drift terms.

**Next proposition:** for the literal fundamental dyadic Wilson square in the
ORIGINAL odd marginal, produce the positive floor

    oddVariance >= 4/(7+10*C^2+4*C^4),  C=marginalScoreCap(w).

The SAME original square, action, OWN mean and odd partition are retained.
This is a quantitative normalization input, not a macro-retention estimate.
The intended completed consumer is the existing `dyadicOriginalNorm` / its
normalization machinery; its exact finite-to-completed join must be exhibited,
not inferred by equating even and odd masses.

**Available inputs and PAPER argument:**
`generalized_linear_ward` and `residual_upper_scaled`,
`lean/YMGap/Continuum/QuaternionHaarGeneralizedLinearWard.lean:106`, `:283`,
with constant OWN mean m and scale t=2*C^2, give 3*m^2<=2*C^2*e.
`energy_le_variance`,
`lean/YMGap/Continuum/QuaternionHaarRelativeCenteredWard.lean:137`, gives
e<=6*(1+C^2)*v. The literal one-occurrence unit-tail geometry supplies
e+v+m^2=4, by `paddedSquare_block_gamma`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareWardMoments.lean:206`.
Consequently 12<=(21+30*C^2+12*C^4)*v. All six actual relative bounds
and positive C are produced by the ORIGINAL marginal machinery in
`BF4ExactSlabFixedSpatialRelativeWardBound` / `MarginalRelativeBound`.
The argument uses no global density minimum, inverse variance, replacement
law, or separately favorable derivative sign. Independent PAPER algebra
review agrees; it is not yet a new kernel-checked theorem.

**Decisive tests:** a zero or merely head-linear source does NOT satisfy the
amplitude-four identity; produce it for the literal unit word. Means may be
zero; cancel only positive scalar C^2 and the actual positive partition.
The floor is nome-dependent, not spacing-uniform. A sharper raw variance
floor alone still does not pay macroscopic time loss or prove continuum
survival. Do not weaken the direct macro condition or any canonical field.

**Verification budget / abandon condition:** bounded implementation in
existing algebra and actual-source leaves, independent complete frozen-source
review and serial focused safe checks, one 20-GiB worker / 12-GiB OS reserve
after every fresh dynamic/process preflight. No full-tree build/audit or limit
increase. Reject a consumer needing an unsupplied geometry/limit premise or
equating different chronological masses. Record observed evidence separately.
No displayed canonical claim changes and no ASCII reprint are selected.

### Observed generic contraction (2026-10-08 UTC)

The PAPER algebra above is now kernel-checked in the EXISTING
`QuaternionHaarGeneralizedLinearWard.lean`. `raw_mean_square_le_energy`
retains the complete signed Ward residual and proves
3*m^2*Z <= 2*C^2*E. `original_score_variance_floor` combines it with the
SAME centered Ward estimate and supplied amplitude-four carrier identity,
producing `scoreVarianceFloor C = 4/(7+10*C^2+4*C^4)` against the OWN
normalized variance. Only positive C^2 and the actual positive Z are canceled;
no nonzero-mean or energy premise is added.

Focused check 1 PASS, exit 0. The six new public gates print no axioms beyond
{propext, Quot.sound}; `scoreVarianceFactor` itself uses none. Independent
review read the COMPLETE frozen 616-line source, rechecked its hash, and
found no defect or changed old API. Fresh preflight found no competing
compiler/runner, 84% free memory and zero swap. One 20-GiB capped worker,
12-GiB reserve, no limit increase or root/full-tree audit.

    /private/tmp/ym-oct8-score-variance-generic1.log
    SHA256 823ea85d265ca3436f6220046e10e27848889c3da6ff65fd95d3109fb3feb854
    Final source SHA256 c90cb8e09b21a30fcf56c7a8f43b7eb428fadcdf0c24a33598f1dca0ac365367

CONTINUE the literal padded-square frame and SAME completed-norm joins;
those are not yet verified by this generic check. Existing prediction-floor
algebra is preserved; the new floor is an additional explicit bound, not the
first same-weight coercivity result. Scaling survival, physical mass, SAME
continuum QFT, every group and Clay remain OPEN. No chart-state change.

### Observed literal-source and completed-norm contraction (2026-10-08 UTC)

The actual join is now kernel-checked in the EXISTING
`lean/YMGap/Continuum/BF4DyadicWilsonSquareWardMoments.lean`:

- `paddedSquare_head_gamma:259` transports the amplitude-four identity at
  full Haar-carrier level, using the existing
  `reindex_blockAngularSquare_carrier`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteAngularSquare.lean:97`.
  It can be inserted under the full original density, unlike a bare-Haar
  integral equality.
- `paddedSquare_variance_score_floor:410` produces the actual loop's active
  selected link and original relative score certificates. Its only guards
  are strict nome, strict spatial padding and
  `endpointRelativeCutoff(w)<=K`; terminal depth is arbitrary. The bound is
  independent of square size, width, depth and every later cutoff at EACH
  fixed nome. The action, OWN mean and actual odd partition are unchanged.
- `paddedSquare_centeredNorm_score_floor:432` retains this floor in the
  actual original completion's time-zero centered norm. It uses
  `varianceLimit_approx` and `varianceLimit_completed_pin`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean:191`, `:236`,
  with explicit cutoff/time/representation thresholds, then
  `centeredVector_diagonal`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:167`.
  This is precisely the moment defining the existing `dyadicOriginalNorm`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:57`;
  no new limit, finite odd/even partition equality or carrier substitution.

Original focused check 3 PASS, exit 0, all three new and seven retained
printed gates exactly {propext, Quot.sound}. Check1 exposed missing namespace
opens and expensive unfolding; check2 required explicit definitional pins.
Repairs added correct opens, kept heavy produced objects locally opaque,
explicitly unfolded the finite variance/time-zero source, and moved a
duplicate local opacity annotation. No theorem type, premise, existing
public API or compiler limit was changed. No source sorry/axiom/classical
input was added; failed elaborations were not accepted as evidence.
Independent COMPLETE frozen final-source review PASS. Successful fresh
preflight: no competing compiler/runner, 84% free memory, zero swap; one
20-GiB worker, 12-GiB reserve, no root/full-tree audit.

    /private/tmp/ym-oct8-score-variance-original3.log
    SHA256 0491f9ce98cbedcd3b95e92ad32a83b541cea3d5d87c0f8cb790ebd8de5690ca
    Final source SHA256 cdbac998d384e5add16bbae625f786f4e9bc107946fba9e959260fa87191ef03

**Next-frontier quantitative screen (PAPER inference, not a new Lean gate):**
write h=1-w and s=side(scale). The already checked
`gap_score_square_ge_one`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialScoreCalibrationObstruction.lean:82`,
gives h*C^2>=1 for 1/2<=w<1. The new explicit formula therefore gives
floor<=h^2. The original absolute loss ceiling in
`centered_dyadic_loss_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:207`, is
384*s^3*h; the existing relative-energy consumer
`dyadic_relative_energy_of_loss_budget`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean:140`,
needs that budget paid by 2*delta times the SAME norm, with delta<=1 to
retain a positive fraction. Using THIS floor as its rational payment would
require 384*s^3*h<=2*delta*floor, which these certificates cannot supply:
their bound-to-bound ratio is at least 192*s^3/h. This says nothing about
the TRUE norm or TRUE energy. Do not turn it into a Yang--Mills obstruction.

CONTINUE the actual action-specific RELATIVE innovation/complete signed
payment, or direct original macro retention. The stronger fixed-nome norm
witness can pay approximation/normalization errors; it does not replace
transmitted-response floors, physical time, scaling survival, SAME continuum
QFT or every-group inputs. Clay and canonical displayed claims remain OPEN;
no ASCII reprint.

## Selected geometric step: lossless terminal marginal curvature (2026-10-08)

Selection before implementation, 23:34 UTC. The previous scalar-floor algebra
cannot improve its C^-4 exponent without new geometric input. The stronger
candidate is the actual lower log-Hessian of the ORIGINAL terminal marginal.
Its source pins already exist in `TerminalLocalSignedGram.source_momentD_pin`
and private `source_fisher_pin`; its nonnegativity without an observable-noise
multiplier was NOT found. No new frontier bundle or changed field is proposed.

For positive kernel P with certified P*dd-d*d>=0 and original positive
spectator/source q, form A=I(qP), D=I(qd), G=I(qdd). Two independent head
copies sharing the SAME tail give

    2*(A*G-D*D) = I(q1*q2*(P1*dd2+P2*dd1-2*d1*d2)).

Multiplication by the positive P1*P2 turns the last integrand into

    P2^2*(P1*dd1-d1^2) + P1^2*(P2*dd2-d2^2)
      + (P2*d1-P1*d2)^2.

Existing copy/Fubini, positive-window and integrated order-reflection APIs
can therefore remove P1*P2 without an inverse-floor cost in the conclusion.
Planned consumer: retain the actual q=all other kinetic factors*S*g_depth
and produced near-flat prefix curvature, obtaining nonnegative ORIGINAL
`A*(DDA+C*|u|^2*A)-DA^2` under every certified outgoing insertion.
All nine actual jets, arbitrary supported frozen direction u, width/depth,
strict nome and computed common cutoff remain. A generic proof alone is not
enough: its ORIGINAL terminal consumer must also be checked.

Predicted scope is integrated curvature order, NOT a polynomial positivity
certificate, complete marginal S*g_n*g_(n+1) curvature, source-specific
signed payment, variance improvement or macro retention. The later PAPER
weighted-Bochner variance route still needs spatial-word curvature transport
and the sharp weighted identity; neither is supplied as an assumption here.
Abandon if a required actual source/jet pin fails or this order already exists.
Verification budget: two focused serialized targets, one 20-GiB worker,
12-GiB OS reserve, fresh dynamic preflight each launch, independent frozen
source review; no full-tree build/audit or limit increase.

### Checked original terminal curvature and exact next geometry input

2026-10-08 23:39 UTC. The selected two-copy proof and its ORIGINAL terminal
consumer now both pass focused Lean verification.

- `conditional_fisher_nonnegative`,
  `lean/YMGap/Continuum/SU2QuaternionConditionalFisherOrder.lean:102`,
  constructs the cleared square certificate, positive product window,
  lossless integrated reflection and the exact factor-two moment pin.
  It admits zero heads/tail and vanishing q. Only the local P has strict
  positive windows; no original marginal, noise or source is inverted.
- `terminal_marginal_curvature_nonnegative_nearFlat`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalLocalSignedGram.lean:840`,
  instantiates that order with actual q=localOutputDensity*g_(n+r), selected
  original heat P, and all nine precomputed frozen second jets. Existing
  `source_fisher_pin` at `:497` identifies A=T(g_(n+r)), DA and DDA.
  The conclusion retains `A*(DDA+C*threeSquare(u)*A)-DA*DA`, under EVERY
  certified outgoing insertion R. C=4+1/(1-w*w) is explicit, nome-dependent,
  and independent of width/depth after the produced common cutoff. No
  non-abelian continuum or beta-uniform spectral claim follows.

Final source hashes:

    ConditionalFisherOrder (203 lines):
    dabeb337d8e07503deae51eb34bfc5cd57b34a5ed0c25b20902f7e4d8eb83513
    TerminalLocalSignedGram (936 lines):
    2e47b268fa344a597a403d01fdf397c5263e20a4c8bf4311d0d85daeb48421da

ROOT's serialized checks used the safe launcher, jobs=1, 20-GiB worker cap
and 12-GiB reserve. Each launch had a fresh memory/process preflight:
83% free reported, zero swap and no competing Lean/Lake/runner worker.
Generic check1 failed only multiline fun-pattern indentation; the three
syntax repairs did not change its mathematical statement. Generic check2
and original check1 completed with exit 0. Their hashes/logs are:

    /private/tmp/ym-oct8-conditional-fisher-order2.log
    b329c2e150587ea8b003697c927df87000471b41de86d44362300844ff883581
    /private/tmp/ym-oct8-original-terminal-curvature1.log
    0fa65a158e85438e5b4f299265468c24220d40dbeced3e078d3225c1bca34eed

The generic new gate and all 16 original/private gates report dependencies
within {propext, Quot.sound}; no sorryAx or Classical.choice. COMPLETE
independent final-source static review of both exact hashes PASS: two-copy
sign/factors, positive multiplier cancellation, original source factorization,
actual marginal pins and frozen coefficients checked. No full-tree build or
axiom audit, limit increase, foreign proof/code import, new hypothesis bundle
or existing public-type change. This uses the paper follow-through's
original-output/cancellation discipline, not a fermion theorem as a YM input.

The parallel NEXT-input review identifies an actual missing geometry pin:
for the literal selected-link spatial plaquette scalar X, prove its frozen
Hessian `sum_ij u_i*u_j*J_i*J_j X = -X*sum_i u_i^2` with arbitrary Haar
insertions. `frozenScalarSecondJet_pin`,
`lean/YMGap/Continuum/SU2QuaternionPairedFrameScalarJets.lean:212`, currently
provides this for the relative scalar, not the original plaquette word.
Available inputs to reuse, not rebuild:

- `oriented_fourWord_first_angularSquare_of_exposure`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteAngularSquare.lean:238`,
  gives the selected word's first-gradient identity with arbitrary insertion.
- `spatialIncidentFaces_length_le_six`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalRelativeBound.lean:70`,
  counts the literal incident factors.
- `polynomialJet_product_curvature_certificate`,
  `lean/YMGap/Continuum/QuaternionHaarPolynomialJetCurvature.lean:49`,
  retains frozen jets, mixed product terms and polynomial costs exactly.

Actual spatial-word radial-curvature transport, integrated product-order
closure for the two terminal factors and sharp weighted paired-Bochner
control remain to be constructed. Existing certificate tensorization cannot
silently consume the new integrated order as a polynomial certificate.
The PAPER kappa^-2 variance route is not yet proved, and even a stronger
finite floor does not itself pay the relative time-loss budget. No main
macro-retention, scaling survival, physical mass, continuum QFT, every-group
or Clay closure; canonical displayed claims remain OPEN and unchanged.

## Selected next geometric identity: literal plaquette frozen Hessian

2026-10-08 23:42 UTC, selection BEFORE implementation. The preceding turn
is PROGRESS: checked original terminal curvature, commit 5817c89b, pushed
to main. The remaining spatial-curvature leg needs the actual plaquette
scalar's frozen Hessian, not another conditional bundle assuming it.

Proposition: at a link occurring exactly once in a four-link oriented word,
each paired diagonal second jet is minus the word scalar and each distinct
symmetrized mixed jet is zero. Hence ALL NINE frozen jets contracted with
arbitrary polynomial coefficients u equal `-X*threeSquare(u)`, retaining
every original Haar insertion. The direct scalar chain-rule/radial-curvature
consumer is not yet implemented; this removes its actual missing second-jet
identity. Do not call the Hessian pin a heat-curvature or survival theorem.

Argument selected: prove the quaternion paired-frame Clifford identity on
ANY head-homogeneous degree-one polynomial using existing active derivative
degree/Euler identities, then transport through the explicit original word
exposure and retain literal face selection. Available inputs:
`QuaternionHaarLinearAngularEnergy.angular_partial_zero`, actual paired
generators, original oriented-word degree, `PairedFrameAt.chain_pairedSecondAt`
and reversible block charts. This avoids exponential orientation cases or
a new conjugation-frame interface. Reversed orientations stay linear;
repeated links are excluded by the existing four-block exposure, not assumed
to obey this eigen-identity. Frozen coefficients are multiplied AFTER jets.

Predicted scope: generic head-linear Hessian plus literal original plaquette
pin only. Costs/moduli, complete spatialWeight curvature, sharp weighted
Bochner and MAIN relative loss remain unproved. Verification budget: bounded
generic/original targets serialized at 20 GiB with 12-GiB reserve and a fresh
dynamic/process preflight per launch; independent complete final-source
review. Abandon/revise if the geometric identity already exists, the actual
word is not head-linear under its exposure, or any transport needs a changed
carrier/action. No new analytic premise, canonical-field change or chart.

## Checked literal plaquette frozen Hessian

2026-10-09 14:35 UTC. The selected finite geometric input is now produced:
`paired_linear_diagonal`, `paired_linear_mixed`,
`frozen_hessian_of_diagonal_mixed`, `paired_linear_frozen`,
`lean/YMGap/Continuum/QuaternionHaarPairedLinearHessian.lean:246`, `:282`,
`:357`, `:384`; and `oriented_fourWord_first_paired_hessian_jets`,
`oriented_fourWord_first_frozen_hessian`,
`oriented_fourWord_any_slot_frozen_hessian`, `plaquette_frozen_hessian`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFrozenHessian.lean:115`,
`:198`, `:212`, `:238`.

The exact degree-one Euler decomposition preserves spectator coefficients.
Signed coordinate jets prove diagonal -X and symmetrized mixed zero; the
ordered mixed derivatives are not declared to commute. Reversible supported
word exposure, scalar cyclicity and the literal face pin preserve all four
distinct physical edges and their orientation. Arbitrary frozen u is
multiplied only AFTER all nine actual jets. Equality retains every Haar
insertion; no original action, source, carrier or marginal is substituted.

Final source SHA-256 (396 / 289 lines):

    QuaternionHaarPairedLinearHessian:
    c516bea4ca53dc054a85a74b0540ee27b3fe7369af5250a39ecd6176bd76a818
    BF4ExactSlabFixedSpatialPlaquetteFrozenHessian:
    5c0312085723447d22d4555f359bb689967f597ea0f6c3a0a22543312ad6c87c

ROOT final generic check5 and original check3 exited 0, without warnings.
Their eight gates contain only {propext, Quot.sound}. Logs / SHA-256:

    /private/tmp/ym-oct9-paired-linear-hessian5.log
    454bf5de62d6e845946228bc5f60168123cec9e44a8b15ab3b5f7a36f1ed8d8f
    /private/tmp/ym-oct9-original-plaquette-hessian3.log
    36c0cf075dfa4ac492871a76a3955de30846108b04f3cc93ab0faa1f48526fa7

Earlier checks exposed raw trailing-zero padding, implicit/namespace issues
and expensive definitional search. Explicit carrier first/second-jet pins,
twelve signed cases and explicit frozen-form definitions repaired these;
no heartbeat, memory or recursion limit was increased. COMPLETE independent
review of both final hashes PASS. Every launch used a fresh dynamic/process
preflight and one monitored 20-GiB worker with 12-GiB reserve; final-turn
preflights reported 86--87% free, zero swap and no competing job.
The semantic-root import was added, but no root/full-tree build or audit ran.

NEXT remains actual plaquette heat radial-curvature transport with produced
jet intervals and cutoff-error certificates, then complete spatial-weight
curvature and integrated terminal product order. Existing certificate
tensorization does not automatically accept integrated order. Sharp weighted
Bochner, useful SAME-action relative loss/direct macro retention, scaling,
physical mass, QFT/every-group and Clay remain OPEN. The canonical displayed
claims did not change; no ASCII reprint. This is our own finite proof, not
an imported fermion theorem or an admissibility-restricted substitute.

## Selected original plaquette radial-to-prefix curvature join

Selection BEFORE the next analytic transport. Reuse the exact selected-edge
first-gradient identity and the newly checked literal frozen Hessian. The
Lagrange identity produces the nonnegative complement
`|u|^2*(1-X^2)-(sum u_i*J_i X)^2` as three supported cross-product squares.
The existing radial and log-concavity certificates then give the full frozen
Jacobi curvature at the SAME literal spatial face and selected physical link.
This removes the missing finite geometry consumer, not the original-prefix
approximation or the complete spatial-weight estimate.

The original-prefix join must additionally retain the actual value, first and
ALL NINE ordered mixed deficit intervals and the explicit positive head floor.
The generic frozen-curvature approximation consumer already exists. Two
bounded Sol implementations supply arbitrary-block raw chain rules and the
literal four-factor plane-jet intervals, and one independent reviewer checks
their exact final sources. ROOT assembles the actual complement/radial join.
No relative-word substitution or differentiation of a Haar equality is allowed.

Predicted outcome: finite, fixed-strict-nome plaquette curvature only; no claim
uniform as nome tends to one, no integrated-order-to-certificate inference.
The decisive tests are the original four distinct edge selection, the frozen
zero direction, all ordered mixed planes, and equality of the actual prefix
to Jacobi plus deficit before any estimate. Revise if a required actual jet
producer is absent or if the approximation budget cannot pay at its computed
cutoff. Verification is serialized narrow checks, one 20-GiB worker and
12-GiB reserve with fresh dynamic/process preflights; no full-tree audit or
limit increase. MAIN relative signed loss/macro retention and Clay remain OPEN.

## Checked literal ORIGINAL spatial-face heat curvature

2026-10-09 14:57 UTC. The selected radial-to-original-prefix join is now
constructed. For each literal spatial face and one of its physical edges,
strict nome w, later computed cutoff K, and arbitrary supported frozen u,
the original polynomial p=heatPrefix(w,K,X) has a Type-valued certificate for

    C*|u|^2*p^2 + p*sum_ij(u_i*u_j*J_i*J_j p)
                         - (sum_i u_i*J_i p)^2,

with C=`nearFlatCurvatureCap(w)+1`. C depends on w, not width, face, K or u.
This is NOT a claim uniform as w tends to one. The produced derivative caps
512/4096 enter the tolerance/cutoff, not C. The consumer is complete spatial
potential curvature, followed by the still-missing weighted-Bochner estimate.

Exact construction and source pins:

| Input / join | Declaration and source |
| --- | --- |
| Reused selected-edge gradient | `incident_square`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdjacentFullAngular.lean:111` (only made public; body/type unchanged) |
| Literal scalar paired-gradient norm | `plaquette_paired_gradient_square`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteGradient.lean:85` |
| Actual raw first/all-ordered-mixed face intervals | `originalFirstInterval`, `originalMixedInterval`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteJetInterval.lean:169`, `:186` |
| Frozen actual cross-product square complement | `plaquette_frozen_complement_certificate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteRadialCurvature.lean:115` |
| Same-face full Jacobi curvature | `plaquetteJacobi_frozen_curvature_nearFlat_certificate`, same source `:246` |
| K+1 original split and raw ordered jets | `prefix_split_pin`, `prefix_first_split_pin`, `prefix_mixed_split_pin`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets.lean:237`, `:246`, `:256` |
| Actual deficit intervals | `deficit_value_interval`, `deficit_first_interval`, `deficit_mixed_interval`, same source `:315`, `:325`, `:345` |
| Computed tolerance/cutoff/cost | `plaquetteCurvatureTolerance`, `plaquetteCurvatureCutoff`, `plaquetteCurvatureCost`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.lean:56`, `:60`, `:66` |
| ORIGINAL full frozen certificate | `plaquettePrefix_frozen_curvature_nearFlat_certificate`, same source `:104` |

The generic `QPolyHaarPairedAtFrozenChain` leaf supplies raw coefficient
chain rules at arbitrary selected blocks, with all nine ordered jets before
multiplication by u. Original-gradient rescaling uses character-one = 2X and
exact quarter cancellation, not an aggregate-gradient/4 inference. The
Lagrange complement uses actual selected-link derivatives, supported on
the original carrier. The radial and log-concavity polynomials use SAME X.
The original-prefix comparison retains its head floor, signed value/first/
mixed deficits, exact K+1 approximant and factor-six matrix-error budget.
No derivative of a Haar equality, frozen coefficient or integrated scalar
is silently inferred. Arbitrary original insertions and ordered orientation
`a,d,conj(c),conj(b)` remain.

Final source SHA-256:

    QPolyHaarPairedAtFrozenChain:
    dd2f8ff8d17ba6b8a725ada66349b0f2370a1c595bb8c506882da41aa7c3eae0
    BF4ExactSlabFixedSpatialAdjacentFullAngular:
    3f9b245cfd2f9bd0cbabae89c693f55bcb63f20573bd180758ef275e8abe833f
    BF4ExactSlabFixedSpatialPlaquetteGradient:
    0720925ce2014917b0f77409579813d92dbb595d472a10397b3f9cb98c8bacb4
    BF4ExactSlabFixedSpatialPlaquetteJetInterval:
    ed5167e2d389583b6768890a7fbb98e578b936a228061718b39b1eb92261bd0c
    BF4ExactSlabFixedSpatialPlaquetteRadialCurvature:
    4063a4f8d758f505976cf22aa51230f832a38979d1452feededc267f98b188eb
    BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets:
    a0db619ffe862d4457d112b50c5e209039e691fbcf8a8b49f82c729793fd4045
    BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature:
    48a992a9c822e4efd70a9bfec15f1b9a7d5ff080117438b86ab23fd7cacb0483

Seven final ROOT focused checks exited 0 without warnings. Their 52 printed
gates (47 new) contain only {propext, Quot.sound}, or are empty. Exact logs
and SHA-256, respectively:

    /private/tmp/ym-oct9-paired-at-frozen-chain2.log
    50c58a2f88ffcc58648c33854da374835e80e180bf96d070d277076ce4b0850c
    /private/tmp/ym-oct9-selected-edge-square1.log
    42bef380e43770de3226daae850f7cf1142a41b3063c4afee252617395a23599
    /private/tmp/ym-oct9-plaquette-paired-gradient1.log
    8a810938199a95efe88ba4c7181db2fa192805a8d8aef31a16013dbcfd882870
    /private/tmp/ym-oct9-plaquette-jet-interval2.log
    7d9c93777834d8c00aeba11e0bd49efdcac4cb7993d85bef79eb6d5e2613da5a
    /private/tmp/ym-oct9-plaquette-radial-curvature2.log
    71f1cc73723b3f57522516756a62ad72fdc38aa5ad6c11ab2b0b8d2b6e3079d5
    /private/tmp/ym-oct9-plaquette-prefix-jets2.log
    5ad755702fdb407cc6a67dd8c6ae7bac5b58c87e5e0b63ae307213271d8934e9
    /private/tmp/ym-oct9-plaquette-prefix-curvature1.log
    e3b8497cdf7a0fb4c722fece5ade09eef1bbac596e098caef008ec056d4147a1

COMPLETE independent frozen-source review PASS for all seven sources
(unchanged promoted body reviewed against the diff). Two bounded Sol
implementation tasks and one independent read-only reviewer; ROOT inspected
all sources and assembled the actual radial/prefix certificate. Earlier
errors were parser layout, notation precedence, namespace/implicit arguments
and the need for decidable Fin cases when returning Type-valued intervals.
All were repaired without changing the mathematical claim or raising limits.
Fresh preflight per launch reported 84--87% free memory, zero swap and no
competing compiler/runner/test process; one monitored 20-GiB worker with
12-GiB reserve. Semantic-root imports were registered, not root-compiled.
No full-tree build/audit/guard, new hole, classical input or analytic bundle.
The three user untracked `(1).lean` files were untouched.

CONTINUE at the complete actual spatialWeight and integrated terminal product
order. The existing six-incident-face count and polynomial-cost tensorization
are inputs, not a proved product join. Integrated order is NOT automatically
a polynomial certificate. Sharp weighted paired-Bochner variance remains
PAPER; even a sharper norm floor cannot alone pay the absolute cubic temporal
loss. SAME-action relative signed payment/direct macro retention, justified
scaling, physical mass, QFT/every-group and Clay remain OPEN. This is our
finite constructive proof, not an imported fermion result. Canonical exact
displayed claims are unchanged, so no ASCII reprint.

### Independent next-consumer block audit

The bounded source review finds the next finite product joins in existing
source: `spatialWeight`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean:70`,
is the literal ordered product; `pairedAt_mul`,
`lean/YMGap/Continuum/QPolyHaarPairedAtFrozenChain.lean:48`, supplies raw first
Leibniz; `polynomialJet_product_curvature_certificate`,
`lean/YMGap/Continuum/QuaternionHaarPolynomialJetCurvature.lean:49`, retains
the mixed product terms. The next bounded finite proposition is raw frozen
first/second product pins, including all nine ordered cells before u, then
the SAME original spatial product certificate at cost six times the new
face cost. Nonincident zero jets use `heatFace_independent`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceIndependence.lean:169`;
the actual partition and count are `spatialFace_partition` and
`spatialIncidentFaces_length_le_six`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalRelativeBound.lean:65`, `:70`.
These are available inputs, not a checked product conclusion.

The integration residue is importantly different. `localOutputDensity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalOutputDensity.lean:55`,
contains UPPER kinetic factors times the LOWER original spatialWeight.
`terminalDensity_independent`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalLocalSignedGram.lean:460`,
is independence of the selected UPPER block N+s; the checked
`terminal_marginal_curvature_nonnegative_nearFlat` at `:840` does NOT
therefore control a selected LOWER spatial link. Its lower kinetic factors
and terminal message are not certified spectator-independent by that lemma.
The existing `weightedHessian_positive`,
`lean/YMGap/Continuum/SU2QuaternionWeightedHessianSignObstruction.lean:101`,
rules out inferring the required integrated log-Hessian sign from positive
terminal/square insertion alone. Do not infer polynomial positivity from
integrated order, or move that upper-block theorem to a lower block.
After the finite spatial product, require actual LOWER-link density/jet/
integration pins or retain and quantitatively pay the signed term.

## Selected complete spatial and ORIGINAL odd-marginal curvature product

2026-10-09 15:03 UTC, selection BEFORE product implementation. Previous goal
turn is PROGRESS: the actual plaquette prefix curvature was checked, committed
as 9626b7d6 and pushed to main. The next finite proposition is a full frozen
curvature certificate for the literal spatialWeight at cost `6*C_face(w)`.
Use raw first/all-nine product rules, original nonincident-face zero jets,
the actual incident count and existing polynomial-cost square tensorization.
No width-extensive cost or independence of incident factors is needed.

Correction/refinement to the preceding block audit: the upper-head proof
does not itself license a lower-input derivative. But its already checked
`sourceMarginalFirst` and `sourceMarginalSecond`, TerminalLocalSignedGram
`:111`, `:117`, ARE the actual lower-output jets of T(a), and its theorem
at `:840` quantifies over EVERY certified outgoing insertion R. The same-
action partial-Haar pins therefore already license the needed lower-output
square insertions. A new generic spectator-independence hypothesis is not
required. Reuse these pins; do not silently reindex an upper-input theorem.

The next integrated proposition is lower frozen log-curvature for the exact
odd marginal `W=V*g_n*g_(n+1)` at active s, cost `6*C_face(w)+2*C_terminal(w)`.
Multiply each actual terminal order by the opposite original factors'
supported squares and the given certified R; combine with the spatial
certificate using the exact frozen product identity. Include n=0/g_0=1.
This gives integrated Haar order only, NOT a polynomial Certificate for W,
an upper Hessian sign, weighted Poincare, sharp variance or scaling survival.

Available inputs: prior original plaquette certificate; pairedAt_mul and
three-sum algebra; FaceIndependence.heatProduct_supported/independent;
LocalRelativeBound.spatialIncidentFaces_length_le_six; actual terminal
next-step and source-marginal pins; arbitrary certified R in the terminal
order. One bounded Sol raw-product implementation, independent read-only
insertion/variance-consumer reviews, ROOT original product construction.
Predict fixed-nome width/depth-independent cost only. Tests: zero direction,
empty incident product, n=0, mixed ordered signs, original V and BOTH distinct
terminal depths. Revise if a source pin or arbitrary-insertion quantifier
is missing; never infer the required sign from positivity alone. Verify narrow
targets serially with fresh host telemetry, one 20-GiB worker and 12-GiB
reserve, no limit increase or full-tree audit. MAIN signed retention and Clay
remain OPEN; canonical displayed claims unchanged.

## Checked complete spatial and ORIGINAL odd-marginal curvature

2026-10-09 15:17 UTC. Observed finite proof outcome, not a paper theorem or
scaling conclusion. The preceding block-warning's claimed absence of lower
output jets is superseded: actual sourceMarginalFirst/Second and arbitrary-R
terminal order DO support this product. No reindexing of an unsupported
lower-input derivative, terminal spectator assumption or sign-dropping was used.

Write FC_s(C,p,u)=C*|u|^2*p^2+p*D^2_u p-(D_u p)^2, with all nine actual
ordered JiJj p taken before multiplying frozen u. The exact raw identity is
FC_s(C+D,pq,u)=q^2*FC_s(C,p,u)+p^2*FC_s(D,q,u). It holds for dependent factors;
the cross terms cancel only after all nine contractions. Certificates square-
multiply on the SAME Haar carrier. Nonincident original factors remain in V.
The literal incident/complement partition and count <=6 give a Certificate
for FC_s(6*C_face,V,u), independently of width at fixed strict nome.

The actual terminal theorem is recast to FC_s(C_terminal,g_m,u) for EVERY
terminal depth m, including g_0=1, on active selected lower-output indices.
Its arbitrary certified insertion allows the opposite original factors'
supported squares. Applying the exact product identity twice gives
H_N[R*FC_s(6*C_face+2*C_terminal,V*g_n*g_(n+1),u)]>=0 for EVERY certified R.
The result remains INTEGRATED order; no Certificate for full W is inferred.
Cost/cutoff are explicit functions of w. No uniformity as w tends to one,
weighted Poincare, variance, useful time survival, physical mass or Clay closure.

### Frozen source and focused verification

All five final narrow checks exited zero with no diagnostics. Twenty-two
printed gates use only {propext, Quot.sound}, including two axiom-free cost/
cutoff definitions. One monitored 20-GiB worker, 12-GiB reserve, fresh
pressure/swap/process checks before EACH launch; telemetry remained 86 percent
free, zero swap, no competing jobs. No full-tree/root audit or limit increase.
Intermediate repairs were parentheses, namespaces, explicit carrier inference
and the actual zero-depth definitional pin, not altered mathematics.

| Declaration | Source path:line | Frozen SHA-256 | Passing log / SHA-256 |
|---|---|---|---|
| pairedAt_mul_mixed; frozenSecondAt_mul | lean/YMGap/Continuum/QPolyHaarPairedAtFrozenProduct.lean:111; :127 | 9f8a56a5631cc18c017d9dcd8e9f0f1f811ca4cff0196f25a73d1e8648eb8b20 | /private/tmp/ym-oct9-paired-at-frozen-product2.log / 594314b58aec612d9ca1783a4190dc53c6567ea2b99d600282d0b1f29ed404d5 |
| pairedAt_independent_zero; frozenSecondAt_independent_zero | lean/YMGap/Continuum/QPolyHaarPairedAtFrozenZero.lean:37; :64 | 1981230f7c8a53415854b4a8ba821090339e9bdeddf276dd3cede06c07e0e818 | /private/tmp/ym-oct9-paired-at-frozen-zero1.log / 15afc54ff844d98f761bd6a25bfbae1d93a61d87c958829f2a1588e9cb3f1f18 |
| frozenCurvatureAt_product_pin; frozen_product_curvature_certificate | lean/YMGap/Continuum/QuaternionHaarPairedAtFrozenCurvatureProduct.lean:60; :98 | 749abc00c096c3a57abd5b887f5767659cbc1b5fe78459a4daf7f72838d8dc68 | /private/tmp/ym-oct9-paired-at-curvature-product2.log / 0aeccfca42e8990177a385120228162c57ffcc06aacf3ba78da93cc2242d869f |
| spatialWeight_frozen_curvature_nearFlat_certificate | lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCurvature.lean:117 | 9eba92e2052ef6da4afb3d6e22172bb48c71c5c9658784bc813a6658451b93d7 | /private/tmp/ym-oct9-spatial-curvature3.log / fd3c222a09082f4dd39f9b7150adec276ded82d5bc4b6cfedf189a53a8f2c46c |
| terminalMessage_frozen_curvature_nonnegative_nearFlat; marginalWeight_frozen_curvature_nonnegative_nearFlat | lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMarginalCurvature.lean:88; :152 | df9577743ed178250d0daa71d7d655a1e393e5c83d6c7d2568b1b29c09c4a182 | /private/tmp/ym-oct9-marginal-curvature4.log / 0a73445bafe6a27e3c6239a7ba3a922442906b2d17b816b8e243d9ffb13a7209 |

COMPLETE independent final-frozen-source review PASS on all five exact hashes
by plaquette_hessian_review; ROOT separately read every complete source and
owns compilation. Bounded Sol raw-product/zero and spatial implementations;
no agent compiler or foreign-code execution. The reviewer verified actual
index/measure, both chronological depths, n=0, ordered signs, certificate vs
integrated-order distinction and no differentiated u.

### Exact next mathematical join (PAPER, not a new premise)

For SAME normalized W, set e=mu_W Gamma(f), v=OWN variance, m=OWN mean.
The current linear-source amplitude identity is e+v+m^2=4; the odd marginal
does NOT imply m=0. A candidate sharper lower variance proof uses:

1. A constructive reciprocal test R_k tending to 1/W on the EXISTING actual
   positive window, with errors paid against all cleared curvature factors.
   Choosing spectator squares alone does not remove the extra factor of W.
2. Selected-frame Fisher IBP from full-W lower log-Hessian, potentially
   I_W<=3B and m^2<=(B/3)e, with the actual paired normalization proved.
3. The drifted weighted Bochner identity and selected source ordered-square
   bound, potentially e^2<=v*(12+B*e). The number 12 is a PAPER candidate,
   not currently produced. The symmetric frozen-Hessian identity alone
   does not control ordered Hessian squares or their commutator terms.

This candidate may remove the two squared-score Young losses behind the
existing C^-4 floor. It is not a new Poincare field or an inhabited sharp
variance claim. Existing six-field unweighted Bochner and paired gradient
pins do not already supply the weighted generator identity. Any amplitude
depending on the selected block must be differentiated literally; a spectator
amplitude may be pulled through only under actual independence.

Decision: CONTINUE the same-W reciprocal/Fisher/Bochner join, retaining MAIN
relative signed payment/direct macro retention as co-primary. Even a sharper
variance floor alone does not pay the existing absolute temporal-loss ceiling.
No canonical displayed claim or scorecard field changed, hence no chart print.

## Selection: lossless SAME-marginal Fisher dual

2026-10-09 15:30 UTC. Prior turn PROGRESS, committed/pushed dfeb7488.
Selected proposition: for every supported signed test h and actual active
selected paired generator J_i, H[(J_i W)h]^2 <= C(w) H[W] H[W h^2],
where W is the literal V*g_n*g_(n+1) and C is marginalCurvatureCost.
No logarithmic score object or inverse-floor penalty is selected.

Square completion converts the already produced integrated curvature order
under EVERY certified insertion R into order of W times a polynomial tilt.
Finite positive-window reciprocal tests then reflect that integrated order
without asserting a polynomial certificate for the quotient. Approximation
errors vanish constructively using the existing explicit cutoff and rational
Archimedean closure. Actual paired Haar IBP gives H[J_i^2 W]=0. A two-variable
quadratic discriminant then proves the dual bound. The finite window may
depend on cutoff/width/depth; the final cost does not, at FIXED strict nome.

Inputs already exist: full original curvature, actual finite lower/upper
window certificates, actual active-block support and angular Haar IBP.
ROOT proves the original-marginal consumer; bounded Sol implements basis pins
and integrated dual algebra; independent read-only Sol reviews exact objects,
signs and quantifiers. Backward review screens source-specific ordered IBP
for a later variance join; no Bochner/Poincare premise is introduced now.
Checks cover signed h, n=0, actual active index, and BOTH original depths.
Abandon this join if arbitrary certified insertion or actual positive window
is absent. One monitored 20-GiB worker, 12-GiB reserve, fresh telemetry EACH
launch; no full-tree audit or limit raise. MAIN signed retention, scaling and
Clay remain OPEN. Canonical displayed claims unchanged; no chart print.

## Checked lossless ORIGINAL paired Fisher dual

2026-10-09 15:35 UTC. Observed finite proof outcome, not an imported paper
theorem or a variance/scaling conclusion. For the literal W=V*g_n*g_(n+1),
actual active selected index s and every supported signed polynomial h:

    H_N[(J_i W)*h]^2 <= H_N[W*h^2] * (C(w)*H_N[W]),
    C(w) = marginalCurvatureCost(w) = 6*C_face(w)+2*C_terminal(w).

The normalized version divides BOTH sides by the SAME positive original odd
partition H_N[W]. Neither terminal mass is substituted. K, width and n remain
in W; both chronological messages remain, including the g_0=1 case. C depends
on strict nome w, with no claimed uniformity as w approaches one.

The exact square completion is
W*tilt = (s*W*h-t*J_i W)^2 + t^2*(C*W^2+W*J_i^2 W-(J_i W)^2).
The previously proved arbitrary-certified-insertion curvature order therefore
orders R*W*tilt for every certified R. The NEW integrated positive-window
reflection uses R=background*reciprocal_k, pays the supported-polynomial
interval error at an explicit cutoff, and removes it by rational invSucc
closure. It never asserts a Certificate for the curvature, quotient or tilt.
Actual paired Haar IBP gives H_N[J_i^2 W]=0. The nonnegative two-variable
quadratic discriminant gives the squared dual bound. Finite approximation
depth/window can depend on K/width/n and h; NO inverse-floor factor survives
in the conclusion. The heat cutoff stays fixed while the reciprocal degree
varies; no circular heat-cutoff selection occurs.

### Frozen sources, narrow checks and independent review

Four final focused checks exited zero, with no diagnostics. Seventeen printed
gates (including two unchanged old dual theorems) use only {propext,
Quot.sound}; basisDirection is axiom-free. No new hole, analytic premise,
classical step, foreign code or limit increase. ROOT read the full sources,
owns the compilation and actual original consumer. Bounded Sol supplied
basis pins and integrated dual algebra; an independent read-only Sol reviewer
attested COMPLETE final-frozen-source PASS on all four exact hashes below.

| Declaration | Source path:line | Frozen SHA-256 | Passing log / SHA-256 |
|---|---|---|---|
| reflection_with_error_of_positive_multiplier_order; haar_nonnegative_of_positive_multiplier_order | lean/YMGap/Continuum/QuaternionHaarIntegratedPositiveWindowOrderReflection.lean:32; :69 | 7d7326d092d2dc999fb1f46712f12a03274c689ed45716272e346da2666a2622 | /private/tmp/ym-oct9-integrated-window-reflection1.log / e6c8d5365dfeec3f6ecaac459e1221ecf76e7f5d06f701b277dd99912b2ba4b0 |
| frozenCurvatureAt_basis_pin; paired_haar_zero; paired_square_haar_zero | lean/YMGap/Continuum/QPolyHaarPairedAtFrozenBasis.lean:103; :128; :154 | da6ac4fcc18f4898dd55f3805683e49679a7f35190bfb03a0c1ec3098b0df69a | /private/tmp/ym-oct9-paired-at-frozen-basis2.log / e0e24608a409598d76ef0ec826cc76be71c91d084c4e85640f893867c86d5eb4 |
| integrated_curvature_signed_dual_bound; integrated_curvature_dual_bound | lean/YMGap/Continuum/QuaternionHaarCurvatureDualBound.lean:256; :282 | 887695a53e3c1078197cb16869764b83b7f4121d5533f284fd3488cd8b282be1 | /private/tmp/ym-oct9-integrated-curvature-dual1.log / c444553a4a6149401fc65a98eb285dd05e2edc8dbce2ce7ec7c32f0c11ff0707 |
| marginal_paired_score_dual_bound; marginal_paired_score_normalized_dual_bound | lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFisherDual.lean:72; :130 | db3faa3c3071ec0d5f18160646cff71dcb986a8ca55f6be5282c39cc99fdf5c7 | /private/tmp/ym-oct9-original-marginal-fisher2.log / efe1262c689fb450d27f9ccc1da4537a22668fa3787d810436a04ab36056b568 |

Fresh pressure/swap/full-process telemetry before EACH launch: 86 percent
free, zero swap, no competing compiler/runner. One monitored 20-GiB worker,
12-GiB reserve. Intermediate repairs were missing namespace, vacuous zero
support, the actual Certificate.one constructor and existing left/right
rational congruence APIs; the mathematical statement was unchanged. Root
imports registered only; no root/full-tree build or audit is inferred.

### Backward consumer and next analytic test

The produced dual bounds the original score paired with any signed supported
test. Alone it does NOT produce a lower interacting variance or a weighted
Poincare inequality. Next join to the literal source's OWN mean and energy,
using actual paired eigen/gradient pins rather than assuming the odd-marginal
mean vanishes. The read-only backward screen offers a source-specific double
IBP route: with u_i=J_i f, H2=sum_ij u_i*u_j*J_i*J_j W,
the two integrations give H[H2]=H[W*K_f], where
K_f=sum_ij J_j*J_i((J_i f)*(J_j f)). The REVERSED ordered derivatives matter.
For the literal amplitude-two source the candidate K_f=48-16*Gamma(f)
requires an actual bracket/source-carrier proof; it remains PAPER, not a new
Lean premise or proof. Existing symmetric Hessian pins do not commute JiJj.

Decision: CONTINUE OWN-mean/energy and ordered-source join. Preserve complete
SAME-action relative signed payment/direct macro retention as co-primary;
a stronger norm floor alone cannot pay the present absolute temporal-loss
ceiling. Nontrivial continuum survival, physical calibration, full QFT,
every compact simple group and Clay remain OPEN. No exact displayed chart
claim changed; no chart reprint.

## Selection: SAME-original mean/energy and ordered source join

2026-10-09 15:42 UTC. Prior turn PROGRESS, a9a07a5d committed/pushed.
Selected next proposition: `3*H[W*f]^2 <= C(w)*H[W]*H[W*Gamma_s(f)]`
for an actual active selected block and supported exact block-degree-one
source f, with W still V*g_n*g_(n+1). Consumer: OWN mean/energy constraint
used with the amplitude-four identity in the sharper variance join. Existing
inputs are the checked per-direction Fisher dual, actual At paired product
rule and Haar zero, block-degree-one Casimir, and the paired/six-plane trace
pin. No head reindexing of W or new analytic premise is necessary.

Parallel bounded Sol task: produce the ordered source double-IBP carrier
K_f=sum_ij J_j J_i((J_i f)(J_j f))=12*f^2-4*Gamma(f), retaining an explicit
selected-independent amplitude pin. Differentiate the exact amplitude pin,
and retain BOTH mixed orders through the symmetric Hessian contraction;
do not assume that paired derivatives commute. The literal amplitude-four
source then gives K_f=48-16*Gamma(f). Independent read-only reviews screen
both the source algebra and actual original mean/variance consumer.

Predicted outcome is a fixed-nome mean bound and source identity, not a
spacing-uniform gap. Decisive checks: constant/zero signed tests, nonconstant
spectator coefficients, inactive-link exclusion, own odd partition, and
bare-Haar K having integral zero. Revise if the actual Casimir/derivative
stability or amplitude pin is absent; no weighted-Poincare field will be
added. Narrow serial checks only, one 20-GiB worker/12-GiB reserve, fresh
dynamic preflight each launch. MAIN signed retention and Clay remain OPEN.

2026-10-09 15:51 UTC refinement: OWN mean and the generic ordered source pin
are now checked. To join them without a log-score object, select the actual
frozen-vector dual on the SAME original W: with DA=D_u W and H2=D_u^2 W,
prove `H[DA*h]^2 <= H[W*h^2]*H[H2+C*W*|u|^2]` for every supported signed h.
Use the produced full integrated curvature with dd=H2+C*W*|u|^2, lambda=0
in the checked signed dual theorem. No sign of H2 is assumed. Support and the
existing actual positive window are the only additional produced inputs.
Consumer is the full signed OWN-centered residual; the source double-IBP
pin will later bound H[H2]. No variance or scaling claim is selected now.

## Observed progress: original mean, vector dual and ordered Wilson source

2026-10-09 UTC. Four final focused checks PASS. The original weight remains
W=V*g_n*g_(n+1), with the actual active physical link and both chronological
messages. `paired_linear_mean_ward` proves the exact degree-one identity
sum_i H[(J_i W)(J_i f)]=3*H[W*f], using actual paired Leibniz/Haar zero and
the block Casimir. Combining the previously checked directional Fisher dual
with three-direction scalar Cauchy gives F^2 <= E*((C(w)/3)*Z). The OWN
normalization uses the SAME positive original odd partition Z=H[W]; it yields
m^2 <= (C(w)/3)*e. Arbitrary spectator coefficients are retained. The literal
character-one plaquette consumer supplies its actual support and block degree;
the active-link guard is not silently removed.

The source algebra separately preserves the ordered sum
K_f=sum_ij J_j J_i((J_i f)(J_j f)). Differentiating the exact amplitude
f^2+Gamma=A and retaining BOTH mixed derivative orders gives
K_f=12*f^2-4*Gamma=12*A-16*Gamma. No commutation assumption or new Lie-bracket
premise is used. The ACTUAL head-swapped padded Wilson-square character has
A=4 under every Haar insertion, hence K_f=48-16*Gamma. This is signed, not
a positivity Certificate or an integrated bound on the original marginal.

The original vector dual retains all nine ordered jets. For supported frozen
u and supported signed h, with DA=sum_i u_i*J_i W,
H2=sum_ij u_i*u_j*J_i*J_j W and G=sum_i u_i^2, it proves

    H[DA*h]^2 <= H[W*h^2]*(H[H2]+C(w)*H[W*G]).

This follows from the actual full integrated curvature and the checked signed
dual with dd=H2+C(w)*W*G and lambda=0. The actual positive window is produced.
H[H2] is NOT assumed nonpositive or discarded. No logarithmic score, inverse
observable, inverse-floor cost or weighted-Poincare hypothesis is introduced.

### Frozen verification evidence

ROOT read the complete sources and owned each serial narrow compilation.
A bounded Sol implementation agent produced the ordered source algebra and
actual padded consumer. An independent read-only Sol reviewer attested
COMPLETE final-frozen-source PASS for all four hashes. Twenty printed gates
admit only {propext, Quot.sound}; `third` is axiom-free. No new sorry, axiom,
analytic premise, classical step, foreign code or limit increase.

| Declarations | Source path:line | Frozen SHA-256 | Passing log / SHA-256 |
|---|---|---|---|
| paired_linear_mean_ward; marginal_paired_mean_square_bound; marginal_paired_own_mean_square_bound; plaquette_character_mean_square_bound | lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFisherMean.lean:113; :156; :217; :243 | 072d642c45bda208db342c8d998f7fc51f8c25bef526bbc929250c9ebc4b71a9 | /private/tmp/ym-oct9-original-fisher-mean6.log / 6e6960dd4a6931496600d4db4a61fd2aec7b2c7d8616591694a09aa6ecd9dc22 |
| ordered_reverse_contraction; doubleIBPSource_pin; doubleIBPSource_amplitude_pin | lean/YMGap/Continuum/QuaternionHaarPairedLinearDoubleIBP.lean:217; :332; :396 | bf7506ba56fb79243a1427fe64a107b40073d3fd89576a9add10d61c8194a058 | /private/tmp/ym-oct9-paired-double-ibp2.log / 21776a1ff8b917a9a6afc13debddcce687d5d61872d23e8ba26ec9a87a24f760 |
| paddedSquare_doubleIBPSource_amplitude; paddedSquare_doubleIBPSource_48 | lean/YMGap/Continuum/BF4DyadicWilsonSquareDoubleIBP.lean:44; :86 | 86716b182153abb36741b498fcfedb82ebd4abdcbe8cb07ae2a7417e0d7d8a67 | /private/tmp/ym-oct9-wilson-square-double-ibp1.log / 7e3885e7b12faaa603e340d81aa1bed223dd0af51f88cd006ef60658d007c0af |
| marginal_frozen_score_signed_dual_bound | lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFisherVector.lean:70 | 8dfdbf8254603a674aa85b9c16e95c4adc11c882d3f3d48c230aa0c55b0cb9c5 | /private/tmp/ym-oct9-original-fisher-vector2.log / 62043e3fd27259fea3c6f563c14fce64e275a5077427149a073964195273f046 |

Fresh dynamic pressure/swap/full-process preflight preceded EACH launch:
85--86 percent free, zero swap and no competing compiler/runner. One monitored
20-GiB worker and a 12-GiB OS reserve. Repairs were missing namespaces/support
APIs, fractional constants represented by variables in the existing integer
ring normalizer, and preventing unnecessary paired-derivative unfolding with
an explicit gradient function. An intermediate default whnf timeout was
resolved without raising limits. Temporary diagnostics were removed before
the final check. Final frozen hashes were rechecked without recompilation.
Root imports are registered; no root/full-tree build or audit is inferred.

### Exact next join and remaining boundary

Next produce the ordered double Haar IBP and the actual coordinate transport
from the head-swapped source to the SAME complete original weight:
H[H2]=H[W*K_f]=48*H[W]-16*H[W*Gamma]. Then consume the vector dual at the
OWN-centered signed test, using the exact centered Ward identity, amplitude
four and the produced mean/energy bound. The proposed inverse-square-curvature
variance floor remains PAPER until this SAME-object join and scalar elimination
are checked. A norm floor alone still cannot pay the present absolute cubic
temporal-loss ceiling. SAME-action relative signed payment/direct macro
retention remain co-primary and OPEN; nontrivial continuum survival, physical
calibration, full QFT, every compact simple group and Clay remain OPEN.
No exact canonical displayed claim changed; no ASCII chart reprint.

## Selection: ordered Haar join on the unchanged original carrier

2026-10-09 UTC. Previous goal turn PROGRESS; 5143a310 committed/pushed.
Next proposition: for u_i=J_i f at the actual selected padded-square link,
H[frozenSecondAt s u W]=48*H[W]-16*H[W*sum_i u_i^2], with W still the
complete original odd marginal. Consumer: the CHECKED original signed-vector
Fisher dual, at the source's OWN-centered test. Inputs: paired Haar zero and
Leibniz, the actual nine ordered frozen jets, the checked literal head source
K=48-16*Gamma, supported paired coordinate transport and product-Haar
invariance. The head swap must move BOTH W and f; it does not identify W with
its reindexing. No commutation, Hessian sign, zero-mean or Poincare premise.

Bounded Sol implements the generic ordered At Haar identity; ROOT owns the
original selected-link consumer and all compilation. Independent read-only
review screens order/transport and the backward centered variance/scalar join.
Predicted outcome: an exact SAME-weight signed Hessian expectation, followed
if the produced inputs suffice by the centered residual inequality. Decisive
tests: constants have zero differentiated source; bare Haar gives zero mean
for K; spectator dependence and signed middle frame must be retained; width,
cutoff, both depths and nome must remain explicit. Revise if transport only
offers unweighted equality. Narrow serial 20-GiB worker/12-GiB reserve with
fresh capacity preflight; no full-tree audit or foreign code. An improved
variance floor alone does not pay the MAIN absolute temporal-loss ceiling;
relative signed payment/direct macro retention and Clay remain OPEN.

## Observed progress: SAME-original signed Hessian and centered residual

2026-10-09 UTC. The selected ordered Haar join and its OWN-centered consumer
are now checked. For the ACTUAL padded Wilson-square character f and a selected
observable block s, put u_i=J_s,i f, W=V*g_n*g_(n+1), Z=H[W], E=H[W*Gamma_s(f)].
The generic identity has no support, positivity or commutation premise:

    H[sum_ij u_i*u_j*J_i*J_j W]
      = H[W*sum_j J_j(sum_i J_i(u_i*u_j))].

The first IBP moves i, the second j; only the finite summation axes are
transposed. The actual source transport retains all coefficient derivatives
and the middle negative paired direction at supported Haar-carrier strength.
The explicit head swap moves BOTH the weight and source, then product-Haar
invariance returns to the original carrier. It never asserts W'=W or raw
coefficient equality for padded reindexed derivatives. The literal source
therefore gives H[H2]=48Z-16E for ANY supported W, including the complete
original marginal at every w,K,n. This is an exact signed identity.

At the computed curvature cutoff and strict nome, the actual vector dual now
has its Hessian term produced, not assumed: for every supported signed h,

    H[(D_u W)*h]^2 <= H[W*h^2]*(48Z+(C(w)-16)E).

The physical active link is constructed from actual padded-loop membership
and strict spatial padding. The literal source degree also produces its
OWN-mean bound m^2<=(C(w)/3)*e. With h=f-m, m the SAME W-normalized mean,
the generic paired Ward identity gives E+b=3H[W*h*f]. Existing normalized
cross and squared-center pins, the actual W certificate and positive SAME
odd partition give H[W*h*f]=H[W*h^2]=Z*v. Thus the NEW original consumer proves

    (3*(Z*v)-E)^2 <= (Z*v)*(48*Z+(C(w)-16)*E).

Here v is the OWN normalized variance, not an even-chain variance, bare-Haar
variance or another source's norm. Both terminal factors remain, including
n=0. The negative -16E correction is retained. No sign of H2 or C-16, no
zero mean, inverse observable, weighted Poincare, analytic premise or physical
time identification is assumed. Scalar normalization/elimination into a
sharper positive variance floor is not a newly checked claim.

### Final frozen checks and independent reviews

Four final focused checks exited zero. Fifteen printed public gates use only
{propext, Quot.sound}; `orderedSourceAt` uses only propext. ROOT read complete
sources and owned compilation and the actual original consumers. Bounded Sol
implemented the two generic Haar/Ward leaves; an independent read-only Sol
reviewer attested COMPLETE final-frozen-source PASS on all four exact hashes.

| Declarations | Source path:line | Frozen SHA-256 | Passing log / SHA-256 |
|---|---|---|---|
| pairedAt_haar_ordered_pair; frozenSecondAt_haar_ordered_source; orderedSourceAt_head | lean/YMGap/Continuum/QPolyHaarPairedAtOrderedDoubleIBP.lean:56; :127; :161 | cddae4542a098515a2b657099c8c7c76312b3d3d59816b91a82f742afa44b662 | /private/tmp/ym-oct9-ordered-at-ibp3.log / 33f65cb14662cf1b6b1a1a556fba143e494b6749d49ef5f4ac36b053d9784b49 |
| ordered_source_head_transport; paddedSquare_frozen_hessian_haar; paddedSquare_original_frozen_hessian_haar | lean/YMGap/Continuum/BF4DyadicWilsonSquareFisherHessian.lean:91; :167; :219 | c4d8e52f8aceb429a67580a67ac3ea8a90693bee75337c03633071f23f76a75b | /private/tmp/ym-oct9-original-wilson-hessian3.log / 4fb3fdae8e9a2b91865f87b80091016fe96b9f77c13607a23e2374bfd56ccef2 |
| pairedAt_centered; frozenFirstAt_centered_gradient; pairedAt_centered_ward | lean/YMGap/Continuum/QPolyHaarPairedAtCenteredWard.lean:39; :53; :72 | 7add95c6dbb3c1bcc5fd7081779356aeb0cde40bea8fadcf5404276b0b65d60a | /private/tmp/ym-oct9-centered-paired-ward2.log / c5fe226e7a1b9b9250bd3bbb09c63dc4a991a16a95482d783af256599d7ea34f |
| paddedSquare_original_signed_vector_dual; paddedSquare_original_own_mean_square_bound; paddedSquare_original_own_variance_fisher_ward | lean/YMGap/Continuum/BF4DyadicWilsonSquareFisherWard.lean:76; :129; :205 | 9e2240887478d9671e94d98de08c83dbb4347d4f6e849ada137b5d351c6d7516 | /private/tmp/ym-oct9-original-fisher-ward2.log / 7074752b7329aa1c00209e4ebe747f0f41fe03835268fde2c2d0a766c585b179 |

Fresh dynamic preflight before EACH launch: 84--86 percent free, zero swap,
no competing compiler/runner. One monitored 20-GiB worker/12-GiB reserve.
Repairs were missing namespace opens, an explicit typed intermediate source
sum/head derivative, explicit HaarCarrierEqv.add for the function alias, and
multi-case environment indentation. No proof statement, action or resource
limit changed. No new sorry/axiom/classical/foreign code; no root/full-tree
build or audit is inferred from registering the new imports.

### Backward quantitative screen and next selection

Read-only source/mathematical review, not a new Lean theorem: normalize by
the SAME Z to obtain (3v-e)^2<=v*(48+(C-16)e). With the mean bound and literal
amplitude four this admits an inverse-square-curvature scalar floor; proposed
27/(340*C^2) remains PAPER. The cost is explicitly nome-dependent, not
near-one uniform: `marginalCurvatureCost`,
lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMarginalCurvature.lean:142,
charges six plaquette costs and two terminal costs. The radial term
`nearFlatCap`, lean/YMGap/Continuum/JacobiProductRadialNearFlatBound.lean:303,
contains 1/(1-w^2); `nearFlatCurvatureCap`,
lean/YMGap/Continuum/JacobiHeatPrefixCurvaturePrecision.lean:65, adds two,
and `plaquetteCurvatureCost`,
lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.lean:66,
and `nearFlatPrefixCurvatureCost`,
lean/YMGap/Continuum/SU2QuaternionPairedFrozenHeatPrefixCurvature.lean:181,
add one. The source-level algebra gives
C=32+8/(1-w^2), so the proposed floor is at most 1-w for strict nome.

That screen invokes an EXISTING checked obstruction only conditionally on
the displayed floor comparison: `no_rational_loss_budget`,
lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean:46,
rules out paying the absolute `dyadicLossBound`,
lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean:47,
384*L^3*(1-w) from such a floor with nonnegative fractions summing at most one.
It is an obstruction to THAT certificate, not to the actual signed time loss
or Yang--Mills theory. No new scalar comparison is represented as checked.

Decision: CONTINUE the COMPLETE SAME-action relative signed payment/direct
macro-retention frontier; do not expand standalone normalization without a
quantitatively useful consumer. The original window consumer
`original_window_budget_macro_ratio`,
lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245, still needs
the actual aggregate cost relative to its OWN block variance. The existing
`blockConditionalRatio_noiseCost_abs_le`,
lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedPredictionPayment.lean:505,
retains original innovation and both chronological masses; neither new local
identity bounds that innovation. Direct signed orbit credit remains an
alternative via `signedOrbit_response_credit_identity`,
lean/YMGap/Continuum/BF4WilsonAllNomePositiveOrbitResponseOrder.lean:696.
The new local dual's connection to a complete time-loss estimate must be
proved, not inferred. Nontrivial continuum survival, physical calibration,
full QFT, every compact simple group and Clay remain OPEN. No exact canonical
chart claim changed; no ASCII reprint.

## Selected experiment: non-null ORIGINAL connected dual (2026-10-09)

Previous goal turn: PROGRESS, `065150f9`, a reviewed source/mass consumer
correction, not a new analytic estimate. The direct-route rate screen found
the bare-transmission necessity and AF geometric-certificate obstruction
ALREADY proved; those tests will not be rebuilt.

New exact proposition: for the actual padded square, predecessor n,
q=V*g_(n+1), R=squareSpectator, PR=P R, OWN-centered psi and
S=Z*oddVariance, prove S<=u*U, U=H[q*PR*psi^2],
u=localUpper(w,4*side)>0. Transport the existing upper endpoint
Certificate q<=uR through positive P, multiply by the actual positive q,
and insert psi^2. The existing centered source-moment pin supplies S.
The existing original odd variance floor gives S>0 at headCutoff<=K;
no stronger Fisher cutoff, lower collar band or new analytic input is
needed. The connected Schur inequality a*Z*U^2<=(G+a*S)*D0, a=w^(12*side),
and original nonnegative energy give (G+a*S)<=S, hence the quantitative
cleared floor a*Z*S<=(u*u)*D0 is predicted. Produce D0>0 and the actual
connected energy reserve energy+a*Z*U^2/D0<=S. D0 is computed rational
data, so its reciprocal can then be constructed, not assumed.

SAME-object consumer: `paddedSquare_energy_connected_overlap_cleared`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareConnectedDualOverlap.lean:284`.
Available producers: `endpoint_localUpperCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:203`;
positive product heat and coefficient/Haar order; `paddedSquare_oddVariance_floor`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareOddVarianceFloor.lean:121`;
`paddedSquare_connected_overlap_cleared`, ConnectedDualOverlap at :230,
and its nonnegative connected moment at :217. Preserve the complete
exterior, source, OWN mean and odd partition, including n=0 and strict
padding. No equality of different chronological masses is used.

Prediction: PASS, with an explicit finite positive connected reserve;
no useful near-one or AF-uniform reserve is predicted. Decisive checks:
do not cancel D0 before proving positivity; do not replace q, PR or the
OWN center; verify that every inequality direction survives signed G.
Abandon/revise if positivity requires assuming a nonzero overlap or the
unproduced scaling conclusion. Verification budget: one new focused leaf
and, only if needed, one narrow dependency check, single 20-GiB worker,
12-GiB reserve, fresh live memory/process preflight before each launch.
Bounded Sol implementation and independent complete final-source review;
ROOT owns compilation. No full-tree audit or resource-limit increase.
This selection is PAPER until the final checks recorded below.

Independent algebra also found a quantitatively sharper consumer for that
non-null proof: the lower endpoint certificate gives l*F<=U for
F=H[R*PR*psi^2], and spectator zero first moment gives D<=F when a<=1.
Since D0<=Z*D, l*D0<=Z*U. Combine this with the connected energy inequality,
and cancel the now-PRODUCED positive D0, to get energy+a*l*U<=S.
The upper-only S<=u*U then gives the NEW cleared linear-collar bound
u*energy+a*l*S<=u*S, or energy<=(1-a*l/u)*S. Its fraction improves the
existing squared collar a*l^2/u^2 without discarding the OWN mean or signed
defect. Bare q=R=1,l=u=1 saturates energy=1-a; this is the decisive test.
The coefficients remain fixed-nome/scale and may vanish along AF, so no
macro survival is predicted. Selected follow-through: a second bounded
actual-source leaf, not a new analytic interface; two focused serial checks
total, plus a narrow dependency only if its olean is missing. Both final
sources require independent complete read-only review. This refinement
is PAPER until verified and must not alter canonical gap/continuum claims.

## Observed result: ORIGINAL connected gain and linear collar (2026-10-09 16:41 UTC)

The selected estimate is now KERNEL-CHECKED at its stated finite scope.
Use the original objects and notation of the selection above. The following
are proved, not newly assumed analytic inputs:

1. Upper endpoint comparison, positive product heat and OWN centered insertion
   give S<=uU. The existing original variance floor supplies S>0, hence U>0.
2. E>=0 and D0>=0 retain the complete connected inequality to give
   aZU^2<=S D0. Thus D0>0, with the cleared quantitative floor aZS<=u^2 D0.
3. The computed reciprocal now yields E+aZU^2/D0<=S and E<S.
4. The original lower comparison gives lF<=U. Spectator zero first moment and
   a<=1 yield D<=F, preserving the full affine a*mu^2 term; D0<=ZD then gives
   lD0<=ZU. Multiplying by aU and cancelling the PRODUCED positive D0 gives
   E+a*l*U<=S. Together with S<=uU this gives uE+a*l*S<=uS.
5. Reciprocal of the explicit positive u and the SAME positive odd partition
   gives normalizedEnergy<=(1-linearBandFraction)*oddVariance, with the
   computed linearBandFraction=a*l/u>0.

The old `squareResponseFraction` is a*l^2/u^2,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:220`.
The new energy theorem has one factor l/u rather than its square. The
comparison of these scalar formulas uses the existing headFloor<=1/32 and
prefixCap>=1 in `BF4ExactSlabFixedSpatialUniformLocalBand`; no new comparison
theorem is advertised. The generic bare q=R=1, l=u=1 saturation test is a
PAPER algebra check, not a newly compiled physical instance.

### Exact verification boundary and independent review

| Public outputs | Source path:line | Final frozen SHA-256 | Passing log / SHA-256 |
|---|---|---|---|
| upper overlap; centered mass/overlap positivity; connected mass comparison; D0 positivity/floor; reciprocal gain; strict E<S | lean/YMGap/Continuum/BF4DyadicWilsonSquareConnectedDualGain.lean:167; :229; :236; :244; :263; :278; :327; :366 | ce6037c8a09ffaa64a19a8d97f33d11a9c6e4306e8e7bf82dd351012ff283247 | /private/tmp/ym-oct9-connected-dual-gain3.log / 3b1f1aea4a01b384d5be054c775e247587dd04b1983a9ecc96e9274b1dd0a1bb |
| lower overlap; dual<=centered exterior; linear D0 comparison; energy reserve; cleared linear band; fraction/positivity; raw/normalized energy bounds | lean/YMGap/Continuum/BF4DyadicWilsonSquareLinearBandGain.lean:105; :142; :177; :200; :236; :260; :266; :275; :310 | cc6a4e17b59020758e3a61b7678e9020b3fb6741cc6d2c8146ecc2c77c9ce75b | /private/tmp/ym-oct9-linear-band-gain2.log / fefc14cb4e4a017daa584ecc32fd4ca3b4a7ecb662ec78a9b080a1be172fb7f7 |

Both final focused checks exited zero. ROOT read complete sources, inspected
all 17 printed gates (only {propext, Quot.sound}), and owned serialized
compilation. Bounded Sol implemented the leaves. Independent read-only Sol
re-read COMPLETE final sources and matched both exact hashes: PASS. The
review checked actual q/Pq/PR, OWN center, affine mean term, signed D0,
positivity before reciprocals, and n=0 predecessor coverage.

Commands, each following a fresh successful dynamic/process preflight:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/BF4DyadicWilsonSquareConnectedDualGain.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4DyadicWilsonSquareConnectedDualGain.olean --log-file /private/tmp/ym-oct9-connected-dual-gain3.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/BF4DyadicWilsonSquareLinearBandGain.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4DyadicWilsonSquareLinearBandGain.olean --log-file /private/tmp/ym-oct9-linear-band-gain2.log
```

Five narrow launches total, not five mathematical experiments: baseline
check1 failed on local-notation quotation projection and missing namespace
opens; check2 left only the missing productMap_neg open; check3 passed.
Linear check1 exposed giant-moment whnf unfolding and an untyped positivity
intermediate; local irreducible attributes and an explicit type/exponent
fixed these, and check2 passed. No heartbeat/memory limit raise or mathematical
statement change. Failed checks and their reported error-recovery `sorryAx`
are NOT counted as verification; no sorry was introduced into source. Live
preflights showed 85--86 percent free, zero swap and no competing compiler or
runner. One monitored 20-GiB worker, 12-GiB reserve throughout. Root import
registration only; no root/full-tree build or audit is implied.

### Decision and residue

PROGRESS: the previously computed possibly-null connected denominator now
has produced strict positivity and an explicit floor; this enables the new
linear collar estimate on the complete SAME original energy. The actual
finite consumer, `paddedSquare_energy_connected_overlap_cleared`, is used
without an alignment hypothesis or discarded connected/mean correction.

CONTINUE the COMPLETE original relative signed payment/direct macro-retention
route. This literal-loop estimate is NOT the warmed source b=T^t(g_stage*psi),
its odd partition is NOT both Z0 and Z1, and no repeated-window retention
follows by substituting these objects. The coefficient remains nome/loop-size
dependent; no useful changing-family lower reserve is proved. The next useful
producer must estimate that actual transferred source with both chronological
masses, or its direct cleared two-mass margin. Do not expand scalar
normalization or a geometric-iteration wrapper as a substitute for that join.
Continuum survival, physical calibration, full QFT, every compact simple group
and Clay remain OPEN. No canonical field/exact chart claim changed; no ASCII
reprint. No foreign proof or repeat literature fetch was used.

## Selected actual-source follow-through: linear initial-energy transport (2026-10-09)

Previous goal turn: PROGRESS, commit `57a1f4d7`, with the non-null connected
reserve and linear collar estimate kernel-checked. Two new bounded read-only
source/mathematical reviews found an EXISTING bridge that the preceding
consumer reconciliation had not included:
`original_block_cost_le_initial_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalEnergyTransport.lean:224`.
It propagates an initial local energy coefficient through the actual positive
symmetric transfer to b=T^t(g_stage*psi), with BOTH distinct masses and no
per-filter accumulation. This does not identify the local literal source with
b; it proves the required transport using Rayleigh-floor persistence and a
fixed terminal envelope.

Exact selected proposition: with stage=n+1, the ACTUAL chronological OWN
center c=middleRatio(stage+1,stage,f), A=g_(stage+t),
b=T^t(g_stage*(f-c)), prove

    clearedRayleighCost(A,b)
      <= (1-linearBandFraction+comparisonEta(n))*Z1*H[V*b^2].

Then divide by the produced SAME positive Z0*Z1 to reach the EXISTING
originalOwnBlockCost/originalOwnBlockVariance definitions, rather than invent
a new source or completion. Available inputs: the last turn's raw linear
energy theorem; `marginalMoment_pin`, FamilyVarianceWard at :64, identifies
the INITIAL local own center with c at that SAME initial stage; the existing
`energy_shifted` and `centered_unprojected_square` in FamilyBandResponse; and
the local-energy transport theorem. Positivity of original energy and the
produced original centered mass give 0<=1-linearBandFraction. No arbitrary-
center generalization or degree-one assumption on b is needed.

Prediction: PASS for all t and admissible finite cutoffs, fixed strict nome,
width and padded loop. This is a real sharper estimate on the actual warmed
source, not a useful macro-window coefficient: 1-linearBandFraction can be
close to one, while the aggregate window needs substantially smaller loss
or a direct multi-step estimate. The inverse-ratio gradient route also has
EXISTING reconstruction/derivative/drift APIs; no new wrapper is selected
there without a small leading-energy estimate.

Decisive tests: retain INITIAL center under every transfer; use center setoid
equality, not recenter at stage+t; keep Z0 and Z1 distinct; allow zero b norms;
do not infer physical/scaling retention by iterating this fixed coefficient.
Abandon/revise if a new survival premise, derivative-degree assumption, or
mass equality is required. Verification budget: one new small actual-source
leaf, one focused serial check plus only required repairs; COMPLETE independent
final-source review, 20-GiB worker/12-GiB reserve, fresh dynamic preflight. No
full-tree build, paper refetch, resource-limit increase or canonical field
change. Selection is PAPER until its final checks are recorded below.

### Independent quantitative screen while the adapter is implemented

PAPER algebra/source review, not a new comparison theorem: the definitions
`linearBandFraction`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareLinearBandGain.lean:260`, and
`channelObservableSquareLinearVarianceCredit`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:370`,
identify delta with a times the existing channel credit at size=side(scale),
up to rational multiplication associativity. The existing
`linearCredit_geometric_ceiling`,
`lean/YMGap/Continuum/BF4OriginalChannelLinearCreditCollapse.lean:45`,
and a<=1 therefore bound THIS coefficient by (1/4)^side<=1/4; d=1-delta>=3/4.
This is a ceiling on a computed certificate, NOT on the actual response.

Consequently, even granting decreasing warmed variances, summing the new
per-lag ceiling over u lags gives only the coefficient 2u(d+eta), at least
3/2 for u>=1. The actual window consumer requires 1-kappa<1 for positive
kappa. This proves no failure of the actual window; it shows why that coarse
summation cannot fund it. The old qualitative geometric response propagation
already exists in `dyadicExcitation_time_geometric_fraction`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean:173`.
Do not rebuild a geometric-iteration consumer or advertise a new qualitative
survival phenomenon. Retain the quantitative actual-b improvement, then
return to action-specific relative smallness or direct multi-step retention.

## Observed result: actual ORIGINAL linear-band transport (2026-10-09 16:57 UTC)

The selected actual-source estimate is now KERNEL-CHECKED at its exact
finite scope. With stage=n+1, K=headCutoff(w)+(n+1), the literal padded
Wilson-square character f, INITIAL chronological OWN center c,
A=g_(stage+t), b=T^t(g_stage*(f-c)), and distinct masses
Z0=H[V*A^2], Z1=H[V*A*T A], the new leaf proves for every t:

    clearedRayleighCost(A,b) <= (1-delta+eta)*Z1*H[V*b^2],
    originalOwnBlockCost <= (1-delta+eta)*originalOwnBlockVariance.

Here delta=linearBandFraction(hw,scale) and eta=comparisonEta(hw,width,n).
Strict nome and side(scale)<width remain. This statement uses the displayed
diagonal cutoff, not a newly proved claim about all arbitrary cutoffs.
No degree/eigenvalue premise on b, norm inverse, final-time recentering,
source substitution or equality Z0=Z1 is assumed.

### Mathematical join

The original raw bound E<=d*S and produced S>0, together with E>=0, give
d=1-delta>=0; delta>0 gives d<=1. `marginalMoment_pin` identifies the INITIAL
local OWN mean with c by Haar/setoid equality. Coefficient congruence retains
the shifted source. `energy_shifted`, `oddMoment_unprojected_source` and
`centered_unprojected_square` then give the exact initial centered-energy
input. The EXISTING `original_block_cost_le_initial_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalEnergyTransport.lean:224`,
transports it through the actual positive symmetric transfer for every t.
Its Rayleigh persistence bridge was absent from the preceding source/mass
reconciliation; this follow-through instantiates it rather than creating
another analytic assumption.

Positive Z0 and Z1 supply reciprocals r0 and r01. The proof retains
(Z0*Z1)*r01=1 and Z0*r0=1, producing Z1*r01=r0 by explicit algebra;
normalizing therefore lands in the EXISTING definitions at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:93`
(`originalOwnBlockVariance`) and :98 (`originalOwnBlockCost`). A possibly
zero transferred norm remains allowed.

### Exact verification boundary

Final source:
`lean/YMGap/Continuum/BF4DyadicWilsonSquareLinearBandTransport.lean`, 290 lines,
SHA-256 `aaa403fcca2923ad8e605954d885e94b3d361813b905d929d591a25b4b7857b2`.
Public declarations and lines:

- `linearBandResidual_nonnegative`, :80;
- `linearBandResidual_le_one`, :104;
- `paddedSquare_initial_centered_energy`, :120;
- `paddedSquare_linearBand_original_block_cost`, :191;
- `paddedSquare_linearBand_originalOwnBlockCost`, :224.

Passing log `/private/tmp/ym-oct9-linear-band-transport4.log`, SHA-256
`2867252e252d67b93cc4c8bd779f34d71ba63594719b0ed6d31f7de383be524d`.
Final focused check4 exited zero; all five printed gates use only
{propext, Quot.sound}. ROOT inspected the complete final source and log.
Independent read-only Sol reread ALL 290 hash-matched lines: PASS for the
initial center, actual b, both distinct masses, zero norms and stated scope.

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/BF4DyadicWilsonSquareLinearBandTransport.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4DyadicWilsonSquareLinearBandTransport.olean --log-file /private/tmp/ym-oct9-linear-band-transport4.log
```

Four serial focused launches total. Check1 failed on namespace/parser/local
unfolding details; check2 passed the first four outputs. Check3 after adding
the normalized output left only the local Z1 let-expression rewrite; its
explicit change to the actual terminal pair made check4 pass. Failed-check
error-recovery axioms are not verification and no sorry was added to source.
No mathematical statement, heartbeat or memory limit was relaxed. Fresh
live preflights before every launch showed 85--86 percent free, zero swap
and no competing compiler/runner. One monitored 20-GiB worker and 12-GiB
OS reserve. The root import is registered; no root/full-tree build or audit
is implied.

### Decision: preserve the improvement; pursue useful smallness

PROGRESS: the sharper initial original-energy estimate now controls the
actual transferred cost with both masses and its OWN transmitted variance.
This is a genuine SAME-object comparison, not a mass/source identification.
The remaining frontier is quantitatively useful complete relative signed
payment or direct multi-step retention on the changing original family.
The preceding PAPER coefficient screen rules out coarse summation as a
useful consumer of THIS ceiling, not the actual survival proposition.

Independent read-only alternative-source review found the signed plaquette
family's footprint-independent w^12 kinetic factor ALREADY proved in
`spatialSpan_fullRange`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`, and
`family_spectator_kinetic`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyLocalBand.lean:259`.
The existing collar certificate is quantitatively insufficient:
`familyResponseFraction_le_ceiling` and
`transported_family_band_linear_budget_false`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFamilyBandCalibrationObstruction.lean:64`
and :151. The SAME-law sharper route retains its complete signed remainder
in `padded_family_energy_relative_ward`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyRelativeWard.lean:332`.
No new useful bound was found there. Preserve all signed family cross terms;
do not call this scalar-character family a continuum field-strength state.
Do not rebuild family, qualitative geometric propagation or normalization
machinery as a substitute for the missing estimate.

Continuum survival, physical calibration, QFT, every compact simple group
and Clay remain OPEN. No canonical displayed claim changed; no ASCII
reprint. No foreign code or repeat paper/literature fetch was used.

## Next selection: test the Fisher coefficient before expanding Ward (2026-10-09 17:03 UTC)

Previous goal turn: PROGRESS, commit `6657795b`; the sharper local energy
now bounds the actual transferred cost at its OWN center with BOTH masses.
Two new bounded read-only Sol screens, with no compilation or literature
fetch, tested alternatives to repeating that weak coefficient.

The direct moment/orbit route supplies no source-specific lower reserve.
`macro_ratio_of_survival_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedLogConvexity.lean:133`,
already consumes a supplied half-horizon survival floor. Positive-orbit
retention likewise consumes a raw floor; signed orbit credit keeps its
negative early covariance. A single scalar contraction mode with rate half
satisfies moment positivity/log-convexity but has doubled-window ratio
half^(2s). Any finite time polynomial which is nonzero on that mode only
rescales its moments; it cannot alter the ratio. This is PAPER selection
algebra, not an original-action counterexample or a new Lean theorem.
No duplicate moment/iteration scaffold is selected.

The lossless Fisher route also has an exact bottleneck. The integrated
score-functional bound in `marginal_paired_score_dual_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFisherDual.lean:72`, is not the
local score-square premise of `active_residual_lower`,
`lean/YMGap/Continuum/QuaternionHaarLocalRelativeWard.lean:148`.
Using the full vector instead retains the actual ordered Hessian in
`marginal_frozen_score_signed_dual_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFisherVector.lean:70`.
That Hessian and the complete signed Taylor remainder must be controlled,
not omitted. No currently supplied arbitrary-signed-family comparison
was found by the reviewer.

Before implementing such a difficult comparison, test its coefficient.
The ACTUAL marginalCurvatureCost is assembled from six spatial and two
terminal costs; unfolding gives C=32+8/(1-w*w) at strict nome. Even the
optimistic replacement angularEnergy<=C*OWNVariance would give the
first-order temporal coefficient (1-w)*C. Its scalar lower bound is FOUR,
not a small quantity near one. Proposed exact proposition:

    4 <= (1-w)*marginalCurvatureCost(w),       0<w<1.

Consequently this computed coefficient cannot pay a target below four.
This is a barrier for THIS certificate, not a lower bound on the true
energy, a variance theorem, a no-go theorem for cancellations or a
Yang--Mills counterexample. Its existing analytic consumer is
`padded_family_energy_relative_ward`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyRelativeWard.lean:332`,
which still retains normalizedRemainder. It justifies pruning a plan that
only replaces the old squared score cap by C and ignores the remainder.

Inputs: exact computed curvature definitions, positive 1-w and 1-w*w,
their factorization, and rational reciprocal/order algebra. Prediction:
PASS with explicit strict-nome guards and no analytic input. Decisive
test: do not confuse a computed UPPER-bound coefficient with a lower
bound on the actual operator cost; near-one behavior must not vanish.
Abandon any extension needing a physical/scaling premise or new wrapper.
Budget: one small scalar leaf, one focused serial check plus local repairs,
COMPLETE independent final-source review; fresh dynamic preflight, one
20-GiB worker/12-GiB reserve. No full-tree build or limit increase.
Selection is PAPER until final evidence is recorded. Return afterwards to
joint signed absorption/direct source-specific multi-step retention.

## Observed result: Fisher coefficient-only branch pruned (2026-10-09 17:09 UTC)

The ACTUAL computed cost formula, denominator pin, strict-nome lower bound
4<=(1-w)*C(w), and exclusion of a target below four are now KERNEL-CHECKED.
This proves insufficiency of THIS coefficient for that scalar budget, not
a lower bound on the actual energy, a false-sign theorem for the original
remainder or a Yang--Mills/continuum obstruction. No family Hessian estimate
is claimed. The decision is PRUNE the coefficient-only replacement, and
CONTINUE combined signed payment/direct source-specific multi-step retention.

Final source:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFisherCalibrationObstruction.lean`,
129 lines, SHA-256
`ebe8d8bcb89e67fe4794b48f666800fef9b8f7f34fa9385555512f2351cb4794`.
Public declarations:

- `marginalCurvatureCost_formula`, :24;
- `marginalCurvatureCost_denominator_pin`, :48;
- `marginalCurvatureCost_nome_defect_lower`, :76;
- `marginalCurvatureCost_not_below_target`, :114.

Focused check2 exited zero; all four printed gates use only
{propext, Quot.sound}. Passing log `/private/tmp/ym-oct9-fisher-calibration2.log`,
SHA-256 `9b566d3325ff867cb4dc33ee9eb599ec1f72c0d6148fb10fe990e926b4a4c884`.
ROOT read the complete final source and axiom output; independent read-only
Sol reread ALL 129 hash-matched lines: PASS. Two serial narrow launches;
check1 found only a factor-order mismatch at positive cancellation. An
explicit setoid multiplication-commutativity step repaired it, with no
statement or limit change and no sorry introduced. Error-recovery axioms
from check1 are not counted as verification.

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFisherCalibrationObstruction.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFisherCalibrationObstruction.olean --log-file /private/tmp/ym-oct9-fisher-calibration2.log
```

Successful fresh host preflights before both launches showed 86/85 percent
free, zero swap and no competing Lean/Lake/pytest/runner. The monitored
checks used one 20-GiB worker and 12-GiB OS reserve; neither stayed live
beyond the initial call. No tree audit, foreign code, resource-limit raise
or routine literature scan. Root import registration only.

### Independent signed-debt screen while checking: actual SU(2) heat algebra

The original channel debt is a signed DIFFERENCE, not a sum of nonnegative
diagonals: `familyChannelTaylorDebt`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelTaylorVariance.lean:107`,
is sum_z weight_z*(R(a_z,a_z*f^2)-R(a_z*f,a_z*f)), with the SAME channel
source a_z. Its exact energy identity at :119 retains that difference.
Bernoulli attenuation positivity does not assign its sign.

PAPER finite sign test, independently checked by ROOT and read-only Sol,
not a new Lean theorem or an original BF4 endpoint instance: on ONE SU(2)
Haar link, choose w=1/2, K>=4, f=chi_1 and a=1+(3/4)*chi_2.
Since chi_2=4*x0^2-1, a=1/4+3*x0^2 is strictly positive. Character fusion
gives a*f=(7/4)*chi_1+(3/4)*chi_3 and
a*f^2=(7/4)*chi_0+(5/2)*chi_2+(3/4)*chi_4. With normalized Haar character
pairings and r_n=w^(n*(n+2))-1+(1-w)*n*(n+2), the actual remainder values
are r_1=5/8, r_2=769/256 and r_3=212993/32768. Therefore

    R(a,a*f^2)-R(a*f,a*f)
      = (15/8)*r_2-(49/16)*r_1-(9/16)*r_3
      = 32503/524288 > 0.

For a=1 and the same f the debt is -r_1=-5/8<0. The two signs refute a
generic sign inference from positive source/weights and Bernoulli mode
multipliers, NOT any original BF4 source-specific sign theorem. Current
source pins: `first_character_square`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatPlaquetteSquare.lean:32`;
private `first_mul_succ` and `square_mul_two`,
`lean/YMGap/Continuum/SU2QuaternionPlaquetteQuarticHaar.lean:44` and :67;
`productRemainder`,
`lean/YMGap/Continuum/SU2HeatProductTaylorRemainder.lean:33`;
`pairRemainder`,
`lean/YMGap/Continuum/SU2QuaternionCyclicModeTaylor.lean:263`.
The narrow review did not find a single public one-link all-spin Haar
orthonormality theorem; this finite pairing calculation uses the explicit
character polynomials and normalized Haar moments and remains PAPER here.

Keep the original coherent square and the full signed debt TOGETHER in
`family_coherent_energy_retained_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCoherentEnergy.lean:263`.
An estimate for that combined quantity or an independent original-source
late-horizon reserve is still missing. Do not replace it by an unproved
debt sign or by an orbit/log-convexity wrapper consuming the same reserve.
All physical, continuum, QFT, every-group and Clay endpoints remain OPEN;
no canonical displayed claim changed and no ASCII chart is reprinted.

## Selected finite test: full-density directional flux versus OWN variance (2026-10-09)

ROOT's new calculation, independently checked before implementation, keeps
the INITIAL spatial family F and its produced Casimir-12 pin. Write
G=Gamma(F,F), W=V*g_n*g_(n+1), Z=H(W), and, for any rational alpha,
A=Gamma(W,F)-alpha*W*G. This DEFINES a residual; no score-alignment premise
or exponential replacement of the original weight is introduced. Put
I=H[W*Gamma(F,G)] and R=Z*H[G*A]-H[W*G]*H[A].
For det_W(f)=Z*H[W*f^2]-H[W*f]^2, the predicted exact identity is

    det_W(12*F-2*alpha*G)
      = 144*det_W(F)-4*alpha*Z*I-4*alpha*R.

An existing positive weight certificate should therefore PRODUCE
4*alpha*Z*I+4*alpha*R <= 144*det_W(F), without inverses, a mass floor,
an alpha sign, or dropping the OWN mean correction. Use the actual six-plane
angular Gamma, not an unproved paired-frame or covariant-Hessian identification.
The original instance must build the eigenpin and W certificate from
`spatialSpan_casimir`, FamilyCasimir:294, and `marginalCertificate`,
ActualMarginalDual:89; `casimir_pair_gamma`, SecondOrderCancellation:153,
and `activeGamma_mul_right`, ActiveCasimirProduct:307, supply the IBP.

Proposed consumer (subsequently REJECTED below): source-specific combined
signed directional-flux payment in the finite spatial-family route.
No existing time-window budget theorem
consumes I and R directly; the source/transfer join remains missing. This is
NOT warmed-source locality, a bound on R alone, a heat-curvature sign, a
survival theorem or a spacing-uniform estimate. Both terminal-message and
spatial responses must remain in A. A zero mass/zero family is allowed.

Budget: one small proof leaf including the literal original instance, one
focused serial check plus local repairs and COMPLETE independent source/log
review. Fresh dynamic host preflight, one 20-GiB worker/12-GiB OS reserve;
no tree audit or limit increase. Stop/revise if an additional analytic
premise, source replacement, unmatched angular normalization or duplicate
already-produced estimate is needed. Selection remains PAPER until checked.

### Observed decision: PRUNE before Lean implementation

ROOT and two independent readers checked the algebra above on paper. It is
correct, including arbitrary signed alpha and zero mass; det_W(F) is
Z^2 times the OWN normalized variance when Z>0, not Z times that variance.
But the actual backward consumer rejects this selection for TWO reasons:

- `familyChannelCurvature`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare.lean:133`,
  uses sum_channel H[b^2*C*Gamma(F,F)], with the ACTUAL `channelSource` b.
  It is not the marginalWeight insertion W above. No equality of those
  weights was produced by the inspected declarations.
- `padded_family_energy_le_retainedChannelVariance`, the same file :357,
  enters that curvature with a MINUS sign. Even under hypothetical score
  alignment, the proposed upper bound on alpha*I is the WRONG direction
  for paying the negative-curvature debt. No bound/sign for R was produced.

No current compensating +I consumer was found in the inspected family
Taylor, coherent-energy, retained-square and paid-square modules. The
estimate is covariance Cauchy--Schwarz specialized through the real initial
Casimir pin, not a new action-response smallness estimate. Implementation
was halted before any Lean file was created; no check ran, no hole changed,
and no theorem is advertised as kernel-checked. Preserve the calculation
as a PAPER diagnostic, not a selected producer or an analytic interface.

The actual next frontend is the COMBINED quantity

    familyChannelErrorBudget
      - (1/2)*(1-w)^2*(familyChannelCurvature
                       +48*familyChannelObservableSquare)

from :357--370, compared against the SAME original
oddMass*oddVariance. Retain the favorable 48-square and actual channel
weights. A lower-curvature estimate or exact signed cancellation must be
proved on those objects; the opposite inequality and the other density do
not meet this consumer. The full time-window/chronological-mass join and
changing-family physical/scaling conclusions remain OPEN.

Execution change: validate inequality DIRECTION and literal weight equality
against the backward consumer BEFORE selecting even a small implementation.
This prunes a route, not a Yang--Mills theory or the Clay target. No canonical
displayed claim changes; no unchanged chart, full audit or compiler is run.

## Selected original pair-curvature reduction (2026-10-09)

After the wrong-sign/different-weight screen, ROOT and an independent
mathematical reader checked a different finite argument. For degree-one
polynomials p,q at the SAME original quaternion link s, the mixed Lagrange
identity is Gamma_s(p,q)+p*q=radius_s*sum_k dp_k*dq_k. Angular derivatives
annihilate the right side. The actual local Casimir product rule therefore
predicts the arbitrary-insertion identity

    C_s Gamma_s(p,q) = 2*Gamma_s(p,q)-6*p*q.

No unit tail, weight sign, score alignment or Hessian premise is needed.
For two distinct physical plaquettes sharing exactly one link, the six
exclusive links contribute 18*Gamma_s, giving the PAPER full identity
C Gamma(fp,fq)=20*Gamma(fp,fq)-6*fp*fq. Orientation is already contained
in the actual degree-one characters. The diagonal producer ALREADY EXISTS:
`plaquette_gamma_casimir`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteCurvature.lean:382`.
Reuse it; do not reprove it. Disjoint pairs give zero. Repeated faces must
take the equal-face branch, not the distinct one-link formula.

Next bounded producer: the local mixed-linear Casimir identity, selected-block
transport, and literal two-incident-face application using produced original
degrees/support. Existing inputs: `angular_partial_zero`,
QuaternionHaarLinearAngularEnergy:110; `headEuler_of_blockDegree`,
SU2QuaternionRatPolyDifferential:788; `blockCasimir_linear`,
SU2QuaternionBlockLinearCasimir:39; `activeCasimirPolynomial_mul`,
SU2QuaternionActiveCasimirProduct:214; and `plaquette_character_degree`,
BF4ExactSlabFixedSpatialPlaquetteDegree:118. These are structural inputs,
not new analytic assumptions. Check the local identity with nonunit and
shared spectator coefficients; no differentiated sphere-equivalence shortcut.

Actual downstream consumer: `familyChannelCurvature`,
BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare:133, which integrates
C Gamma(F,F) under its unchanged ACTUAL channelSource b^2. Full-pair
localization/exclusive-link Casimir, signed ordered-pair assembly and a
favorable weighted comparison still remain; no existing whole-family
theorem consumes just the local identity. The planned full expansion
retains coefficient products and duplicate-list multiplicity. It exposes
the correct curvature object, not a variance/retention bound by itself.

Budget: a compact local proof plus literal physical instance, narrow serial
checks with complete independent final-source/log review, fresh dynamic
preflight, one capped 20-GiB worker/12-GiB reserve. No full audit, resource
increase, new hole or assumed-input interface. Stop/revise on a unit-tail
premise, action replacement, unchecked derivative transport or duplicate
producer. Selection is PAPER until kernel evidence is recorded.

### Observed local decision: CHECKED; full pair/family comparison remains OPEN

Four exact public producers passed their dependency gates:

- `headGamma_linear_casimir`,
  `lean/YMGap/Continuum/QuaternionHaarMixedLinearCasimir.lean:222`;
- `blockGamma_linear_casimir`, the same file :272;
- `incident_pair_gamma_casimir`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSharedFaceCurvature.lean:141`;
- `distinct_pair_activeGamma_localizes`, the same file :170.

The local proof keeps arbitrary supported, signed, shared spectator
coefficients. It includes equal/zero polynomials and one-block carriers;
no unit-tail assumption is used. Euler and a finite mixed-wedge identity
reduce Gamma+p*q to the spectator gradient dot product on the actual
sphere. Only tangential angular derivatives transport that carrier equality;
an explicit supported head swap produces every selected link. The original
instance uses actual canonical oriented face words and produced degrees.
Localization uses distinct-face geometry and physical-index injectivity,
not an assumed absence of cross terms.

Accepted source/log SHA-256:

| target | source | accepted log |
|---|---|---|
| `QuaternionHaarMixedLinearCasimir` | `388db6f0a5b840d3b1f8840d2c020fec9f3d2a446218dee1a32ede743034a2e1` | `0f883bbaf34cd988c33ebaa52543923d14756d42929af1e54c7a8657fb1063f9` |
| `BF4ExactSlabFixedSpatialSharedFaceCurvature` | `7e7c587c9582e43769072a70e1a204fd3a63258a610d36e9e749b58d1498fdf7` | `6c78c4f4f1a4b3b8cbbb71cbd45e582e2953c3e5cb69c3bd1608fffc9efc4cb8` |

Exact accepted commands, from the repository root:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/QuaternionHaarMixedLinearCasimir.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/QuaternionHaarMixedLinearCasimir.olean --log-file /private/tmp/ym-oct9-mixed-linear-casimir3.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSharedFaceCurvature.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSharedFaceCurvature.olean --log-file /private/tmp/ym-oct9-shared-face-curvature7.log
```

Every accepted gate reports exactly {propext,Quot.sound}. ROOT reviewed
complete sources and logs; the independent reader reread both complete
FINAL sources and accepted logs, matching all four hashes, and returned
PASS. Local checks1/2 and physical checks1--3 failed elaboration and are
not proof evidence. Physical check4 compiled but FAILED the axiom gate;
diagnostic checks5/6 isolated core `List.nodup_range` as carrying
`Classical.choice`. Reusing existing constructive `range_nodup`,
`lean/YMGap/Continuum/CayleyParentInj.lean:124`, removed that dependency.
No classical quarantine, gate relaxation or duplicate range proof.
Each launch had a fresh dynamic memory/swap/process preflight: 86 percent
free, zero swap and no competing compiler/test/runner. All runs finished
within their initial call; no live long job, full-tree audit, broad metric,
new hole or resource-limit increase. Root imports are registered, not
root/tree checked.

NEXT mathematical join remains PAPER: for an EXCLUSIVE link b, prove
`C_b(Gamma_s(fp,fq))=3*Gamma_s(fp,fq)`. This is the Casimir of the SHARED
mixed Gamma, not the exclusive-block Gamma (which vanishes). Distinct-block
angular degree preservation and actual independence/support supply the
short route; no theorem currently supplies the full six-link sum here.
The full distinct-pair `20*Gamma-6*fp*fq` and ordered-family assembly are
therefore NOT asserted as checked.

Independent PAPER family algebra predicts

```text
C Gamma(F,F)+48*F^2
  = 20*Gamma(F,F)
    +48*sum_distinct_disjoint c_p*c_q*fp*fq
    +42*sum_distinct_one_overlap c_p*c_q*fp*fq
    -192*sum_equal_geometric_face c_p*c_q.
```

All sums are ORDERED occurrence pairs. Equal geometric faces include
every duplicate-position pair; their coefficient sum regroups by the
square of each face's TOTAL signed coefficient. The remaining channel
insertions are the actual H[b_z^2*fp*fq] and H[b_z^2], not automatically
OWN marginal covariances. Signed 42/48 cross products remain unpaid.
This is our calculation, not a theorem imported from the fermion paper.
Main chronological retention, changing-family survival, physical mass,
continuum/QFT, every-group and Clay remain OPEN. No canonical chart claim
changed, so no unchanged ASCII chart is reprinted.

## Selected full original shared-face Casimir join (2026-10-09)

Previous goal turn: PROGRESS, checked and pushed `93257639`. The active
goal and all continuum/Clay requirements are unchanged. ROOT and the
independent reader again checked the full-pair formula on PAPER:

    C Gamma(fp,fq) = 20*Gamma(fp,fq)-6*fp*fq.

Scope: distinct actual spatial faces in the SAME nonperiodic physical
slice, with a supplied common boundary link; actual active C and Gamma
on range(N width), arbitrary Haar insertions. No nome/cutoff/depth or
tail-unit premise belongs in this structural identity. Available inputs:
`incident_pair_gamma_casimir` and `distinct_pair_activeGamma_localizes`
in `BF4ExactSlabFixedSpatialSharedFaceCurvature`; actual incident degree,
off-row independence, and the four-slot length in `ChannelActiveMoments`.

Predicted short argument: a raw angular derivative in another block
preserves selected-block degree. Thus each exclusive link contributes
3*Gamma_s to C_b(Gamma_s), and an outside link contributes zero. The
shared contribution is already 2*Gamma_s-6*fp*fq. A row-count assembly
can count each face's four links instead of adding a new seven-link
enumeration: 3*(4+4)-4=20, with the shared product term retained.
The exclusive-block Gamma_b itself vanishes; it is NOT the quantity
being differentiated in that contribution.

Actual backward consumer remains `familyChannelCurvature`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare.lean:133`,
and the SUBTRACTED combined curvature-plus-48-square at :357. Root and
the independent reader explicitly checked a decisive sign degeneracy:
at the unit field, one-overlap faces with F=fp-fq have F=Gamma(F,F)=0,
but the PAPER combined expression C Gamma(F,F)+48F^2=-720. Equal-face
branches contribute -384, the two signed overlap products -336. This
refutes automatic pointwise nonnegativity, NOT an original weighted
Haar estimate, Yang--Mills theory or scaling trajectory. Do not drop
signed channel cross moments after the exact assembly.

Budget: one generic exclusive-degree/Casimir leaf and one original
full-pair assembly leaf, with bounded parallel implementation and
independent read-only mathematical/source review. All compilation is
serial via the monitored launcher, 20-GiB worker/12-GiB reserve and a
fresh dynamic preflight each launch. No full-tree audit, resource raise,
new hole, assumed analytic interface or unrelated refactor. Stop/revise
if a unit-tail/action replacement or unbounded geometric enumeration is
needed. Selection is PAPER until exact kernel evidence is recorded;
the signed weighted comparison and chronological/scaling join remain OPEN.

### Observed exclusive/outside-slot producer

`QuaternionHaarExclusiveMixedCasimir.blockGamma_degree_of_ne`,
`lean/YMGap/Continuum/QuaternionHaarExclusiveMixedCasimir.lean:111`,
proves raw selected-block degree preservation away from the differentiated
block, including zero-coefficient derivative terms. Its supported mixed
gradient producer (:126), exclusive positive-Casimir-three identity (:148)
and outside coefficient-zero identity (:166) use the SAME polynomials and
carrier. No spectator-unit, sign, decomposition or analytic premise is added.
The exclusive contribution differentiates the SHARED Gamma, not the zero
exclusive Gamma itself. ROOT read the complete 180-line source; independent
complete final-source/log review PASS.

Accepted focused check1:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/QuaternionHaarExclusiveMixedCasimir.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/QuaternionHaarExclusiveMixedCasimir.olean --log-file /private/tmp/ym-oct9-exclusive-mixed-casimir1.log
source SHA256 b0c8e4c610e754dc1381461a648b164594439b09feb7e6c56a1660c9d797d61d
log SHA256    75eafc0b266688e23ef2060d1b1e3b672ece1c13b68ff09021c11ab74da300c4
```

All four printed gates are exactly {propext,Quot.sound}; no warnings/errors.
This is a finite actual producer, not full pair/family or weighted payment.
Full original physical assembly check1 failed on local-let/Boolean
simplification and a permutation-proof layout; its printed `sorryAx`
comes from elaboration errors and is NOT accepted proof evidence. No source
`sorry`, axiom or weakened field was introduced. Repair remains bounded to
the selected physical leaf; accepted final evidence will be recorded separately.

### Observed full ORIGINAL pair join: CONTINUE

`distinct_pair_sharedGamma_full_casimir`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFullSharedFaceCurvature.lean:289`,
and `distinct_pair_full_gamma_casimir` (:326) now prove the full
`C Gamma(fp,fq)=20*Gamma(fp,fq)-6*fp*fq` identity. Scope: distinct canonical
spatial faces with a supplied common physical link, full original-slice
active C/Gamma and arbitrary Haar insertions. The actual incidence counts
are produced as 12G+12G, then exactly one correction -4G-6fp*fq. No
seven-slot premise, unit-tail assumption, periodic claim or weight substitution.
Full-Gamma transport uses the existing in-range Haar-carrier Casimir theorem,
not raw differentiation of an arbitrary Haar-carrier equality.

ROOT read the COMPLETE final 344-line source and accepted log; independent
complete final-source/log review PASS with matching hashes. Accepted check2:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFullSharedFaceCurvature.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFullSharedFaceCurvature.olean --log-file /private/tmp/ym-oct9-full-shared-face-curvature2.log
source SHA256 009e49b27d46fc27d8062685496ce93ef544e24ed50465853fcefb20cbf9ed7f
log SHA256    49025e344ebea3a5060b706056ac84c82a5a2cd7cd99a0326b63321da566df4c
```

Both gates exactly {propext,Quot.sound}; no errors or `sorryAx` in the
accepted log. One harmless unused-pattern variable warning at :194 remains.
Check1's local-let/Boolean/layout failures are superseded, not accepted
evidence. Each physical launch had a fresh live pressure/swap/process
preflight: pressure-free capacity 86%, zero swap, no competing compiler/test
or Runner job found. Both finished during their initial calls; no live long
job or repeated polling. Root imports are registration only, NOT root checking.

NEXT consumer-directed join: the literal occurrence fold `spatialSpan`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilySchedule.lean:61`,
must expand Gamma in both arguments into ORDERED coefficient-level pairs.
Public `activeGamma_symm` (:344 of `SU2QuaternionActiveCasimirProduct.lean`)
and `activeCasimir_add`/`activeCasimir_smul` (:242/:263 of
`BF4ExactSlabFixedSpatialFamilyCasimir.lean`) are available; the additive Gamma
and fold helpers found by the read-only inventory are currently private.
Use existing equal-face and disjoint branches, retaining signed coefficients
and repeated geometric faces. The family identity remains PAPER; actual
weighted lower control/joint debt, OWN warmed variance, BOTH chronological
masses, justified scaling, physical/QFT/every-group and Clay remain OPEN.
No new analytic wrapper or canonical chart claim is selected or closed.

## Selected ordered ORIGINAL signed-family curvature assembly (2026-10-09)

Previous goal turn: PROGRESS, checked and pushed `82b2cde0`. The next
structural target is on the SAME original full slice, not a new action:

    C Gamma(F,F)+48 F^2 = 20 Gamma(F,F)+R(F),
    F = spatialSpan width c qs.

R is a sum over ORDERED occurrence pairs in qs x qs. Each pair retains
c(p)*c(q), including repeated geometric faces and arbitrary signs. Its
geometric remainder is -192*1 for equal faces, 42*fp*fq for distinct faces
sharing a link, and 48*fp*fq for disjoint faces. The actual Boolean overlap
test uses the finite boundary edges; no hidden classical case split or
assumed partition is selected. Available forward inputs: the checked full
shared-face law, `PlaquetteCurvature.plaquette_gamma` and
`plaquette_gamma_casimir`, and `DisjointFaceEnergy.blockGamma_zero` (:104).
Coefficient-level bilinear/ordered folds must be produced before lifting
them through Haar-carrier equality; repeated occurrences are not deduplicated.

Actual consumer: `familyChannelCurvature` plus
48*`familyChannelObservableSquare`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare.lean:133/:145`,
SUBTRACTED by `padded_family_energy_le_retainedChannelVariance` (:357).
Preserve each actual channelSource b_z and nonnegative channel weight. The
predicted exact channel join separates the positive 20*Gamma moment from
the SIGNED remainder; only the former may be discarded to give a lower
bound. R still needs action-dependent payment relative to OWN variance
and BOTH chronological masses. The unit-field F=fp-fq test gives -720 on
PAPER, so neither pointwise nor weighted sign is assumed.

Budget: one generic finite-fold leaf and one original classified-pair/family
consumer leaf; bounded parallel implementation and read-only math/source
reviews, all checks ROOT-only and serial20GiB/12GiBreserve after fresh live
preflights. No new hypothesis/interface, sorry, axioms, resource increase,
tree audit, metric or routine paper scan. Revise if coefficient congruence,
actual channel identity or constructive finite classification cannot be
produced within this scope; do not replace them by premises. This selection
is PAPER until accepted final checks/reviews are recorded. Weighted payment,
justified scaling, physical/QFT/every-group and Clay remain OPEN.

### Observed ordered-family decision and accepted evidence (2026-10-09)

**PROGRESS, not scaling closure.** The selected ORIGINAL ordered-family
identity and actual channel join are now kernel-checked. The generic
`lean/YMGap/Continuum/QuaternionHaarGammaFiniteSum.lean` expands bilinear Gamma
(:162, `activeGamma_finitePolySum_pair`), the SAME product fold (:186,
`finitePolySum_mul_pair`) and original Casimir (:204,
`activeCasimir_finitePolySum`). Every signed rational scale and repeated list
occurrence is retained. No support/degree/analytic premise is required for
these coefficient identities; coefficient equivalences are lifted before
transport by the Haar-carrier Casimir producer.

Physical producers/consumers, all in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedFamilyCurvature.lean`:

| line | declaration | checked scope |
| --- | --- | --- |
| 76 | `pairRemainder` | Actual geometric equal/shared/disjoint classifier; -192, 42*fp*fq, 48*fp*fq. |
| 152 | `pair_curvature_remainder` | Original full pair identity under every Haar insertion; physical membership guards. |
| 198 | `familyPairRemainder` | Ordered occurrence pairs with signed c(p)*c(q); repeats not deduplicated. |
| 266 | `family_curvature_remainder` | `C Gamma(F,F)+48 F^2 = 20 Gamma(F,F)+R(F)` on original spatialSpan. |
| 300 | `familyChannelGradient` | Actual b_z squared insertions and original product channels. |
| 310 | `familyChannelPairRemainder` | SAME actual projected terminal source, spectator blocks and channel weights. |
| 332 | `familyChannel_curvature_remainder` | Exact `curvature+48*square = 20*gradient+channelR`; no sign/nome bound for equality. |
| 384 | `familyChannelGradient_nonnegative` | Produced supported square certificate for assembled Gamma; nonnegative Gram weights for 0<=w. |
| 408 | `familyChannelPairRemainder_le_curvature_square` | Correct LOWER direction for the quantity subtracted by the actual retained-square consumer. |

The classifier's false-disjoint branch extracts a finite common-link witness
constructively; its existential is only used to prove a proposition, not erase
a required computational output. Equality means geometric face equality, not
list-position equality. Mixed pair Gamma terms are not individually positive.
Only after assembly may the 20*Gamma(F,F) credit be discarded. Neither R nor
its actual weighted moment receives a sign or OWN-variance bound.

Accepted checks, ROOT-only/serial, each exit 0 during its initial call:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/QuaternionHaarGammaFiniteSum.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/QuaternionHaarGammaFiniteSum.olean --log-file /private/tmp/ym-oct9-gamma-finite-sum2.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedFamilyCurvature.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedFamilyCurvature.olean --log-file /private/tmp/ym-oct9-signed-family-curvature2.log
```

Generic final source SHA256:
`9b98758d6ff1c5da6c092c86db6eb24fa607064ce876d5e3ff08fb8421c095c2`.
Accepted generic log SHA256:
`8d386d3a012c98c1d64a0b141d093673a39752dcd52a0b131eb63237f2441a0a`.
Physical final source SHA256:
`24b420eb2757ca8c020b895a0f8b22e08a3b0dbd3f0c2492705d472dc111614a`.
Accepted physical log SHA256:
`914c4889ccd3188e27db67fa3c05a2e5b82c98225f8dca2a00eed0b873b29227`.

Generic check1 failed on missing opened derivative/neg namespaces; physical
check1 failed on namespace resolution, a Haar parameter name and missing
support namespace. Their elaboration placeholders/`sorryAx` are NOT accepted
evidence. No theorem, hypothesis, equation or resource limit was weakened to
repair them. Final generic check2 has 12 gates within {propext,Quot.sound};
physical check2 has nine gates exactly that pair. No final warnings/errors.
Complete independent generic final-source/log review PASS; two complete
independent physical final-source/log/math reviews PASS, exact hashes verified.
Fresh live preflights before every launch: 85--86% pressure-free capacity,
zero swap, no competing compiler/test or Runner job found. The first sandboxed
process inspection was denied; approved read-only inspection succeeded before
compilation. No long job/polling, pressure event or foreign process mutation.
Root imports are registration ONLY, not root integration checking. No tree
audit/metric, new hole, axiom, analytic interface, CI/resource or chart change.

**NEXT quantitative producer, still OPEN:** at the actual positive-depth
terminal channels, estimate the whole

    errorBudget - t*(20*gradient+channelR),   t=(1/2)*(1-w)^2,

against the SAME `oddMass*oddVariance` of
`padded_family_energy_le_retainedChannelVariance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare.lean:357`).
Retain favorable gradient/square and signed cross credits until combined with
the actual cubic/omitted errors. Do not replace this weight by W=V*g_n*g_(n+1)
or claim the ordered cross moments are already OWN covariances. The lower
bound alone pays nothing relative to that variance; full temporal/BOTH-mass
conversion and warming require their own actual-source producers. A useful
changing-family/scaling estimate, nontrivial continuum survival, finite positive
physical mass, full SAME-theory QFT, every group and Clay remain OPEN. No
canonical displayed claim closed, so no unchanged ASCII chart was reprinted.
