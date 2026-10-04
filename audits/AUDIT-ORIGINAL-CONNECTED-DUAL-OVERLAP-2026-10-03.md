# Original connected dual overlap

## Checked result and boundary

After `eec4083`, source-orthogonal projection improves the actual signed
Wilson-square overlap bound. The complete original energy satisfies

    E*D0 + a*Z*U^2 <= S*D0,
    D0 = Z*D - a*m^2,     0 <= D0 <= Z*D.

Here m is a computed SIGNED mean mismatch, not a hypothesis that it vanishes.
Two focused checks passed 15 permitted axiom gates. This is an unconditional
finite improvement under the existing original-source guards, not a useful
scaling estimate or continuum survival theorem. The constructive Clay target
remains OPEN.

## Forward construction: source-norm-cleared projection

`lean/YMGap/Continuum/GNSOrthogonalDualProjection.lean:36` `clearedDual`
constructs t0=B(q,q)*t-B(q,t)*q in the supplied SAME rational GNS form.
`:40` `schurRemainder` is B(q,q)*B(t,t)-B(q,t)^2. The declarations
`:53` `clearedDual_orthogonal`, `:65` `clearedDual_mixed_pin` and
`:81` `clearedDual_norm_pin` prove, respectively,

    B(q,t0) = 0,
    B(x,t0) = B(q,q)*B(x,t)           when B(x,q)=0,
    B(t0,t0) = B(q,q)*schurRemainder.

`:106` `schur_nonnegative` includes a null source. `:118` `cleared_bound`
uses only B(x,q)=0 and B(q,q)>0 to cancel one positive rational factor:

    B(q,q)*B(x,t)^2 <= B(x,x)*(B(q,q)*B(t,t)-B(q,t)^2).

Neither a test norm nor an excitation norm is inverted or assumed positive.
All construction and pairing identities use the supplied original form.

## Original Wilson specialization and causal join

All following concrete declarations are in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareConnectedDualOverlap.lean`.
`:70` `original_kinetic_mass_pin` identifies B(q,q) with the SAME original
odd partition at EVERY depth. For the overlap consumer the chronological
depth is d=n+1; q=V*terminalMessage_d. The test keeps the full predecessor n
and exterior through the existing `squareSpectator`. The form is the actual
active product heat, B(u,v)=H[u*P(v)], not an independently supplied form.

`:86` `squareSpectatorMeanMismatch` defines

    m = H[q*P(R)*psi],
    psi = f-mu,   mu = the OWN original odd-law mean at d.

`:96` `squareConnectedDualMoment` defines D0=Z*D-a*m^2, where
a=w^(12*side), Z is the original odd partition, and D is the existing
affine-corrected spectator dual moment. The original parameters remain
explicit: rational 0<w<1, K>=headCutoff(w), n, scale and width>side(scale);
the overlap/energy inequalities also retain the existing 1<=K guard.
No beta/spacing/volume-uniform coefficient is asserted. D0 and m depend on
the actual original parameters; they are not opaque uniform constants.

`:143` `paddedSquare_centered_kinetic_source_zero` pins B(x,q)=0 for
x=q*psi by the original OWN-center first-moment theorem. The private
`dual_kinetic_pins` at `:146` retains all affine terms:

    B(x,t)=a*U,   B(q,t)=a*m,   B(t,t)=a*D,
    t=R*(f-a*mu),   U=H[q*P(R)*psi^2].

The private `connected_schur_pin` at `:196` pins the Schur remainder to a*D0.
`:217` `paddedSquare_connectedDualMoment_nonnegative` proves D0>=0,
including D0=0. `:230` `paddedSquare_connected_overlap_cleared` then gives

    a*Z*U^2 <= (G+a*S)*D0.

Here G is the ACTUAL signed heat defect and S=Z*OWNVar at the SAME d.
The existing kinetic diagonal is G+a*S; no sign assertion for G is inserted.
`:270` `connectedDualMoment_le_unprojected` proves D0<=Z*D by the explicit
nonnegative square a*m^2. Strict decrease is NOT claimed; m may be zero.
Compared with the old bound multiplied by Z, the numerator is the same and
the denominator is no larger.

`:284` `paddedSquare_energy_connected_overlap_cleared` uses the existing
COMPLETE original energy identity E=(1-a)*S-G, yielding
E*D0+a*Z*U^2<=S*D0. No bare-source replacement, fringe projection, stationary
ground premise, discarded exterior, dual inverse or surviving-norm inverse
enters this join. Zero excitation/dual cases remain in the statement.

## Backward frontier: missing alignment, not another strictness wrapper

The completed macro-response consumer remains
`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`
`completed_reference_ratio`. The alternative aggregate signed-window consumer
is `lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`
`original_window_budget_macro_ratio`. Neither original analytic input is
discharged here.

The sufficient analytic alignment target suggested by the checked cleared
inequality is

    a*Z*U^2 >= (1-epsilon)*S*D0

on a JUSTIFIED changing family, with positivity paid if D0 is cancelled.
This is a MISSING input, not a new Lean theorem, assumed field or certificate.
It is only an optional stronger producer, not a necessary survival condition:
the later source review in
`audits/AUDIT-SURVIVAL-ENERGY-VERSUS-DUAL-SLACK-2026-10-03.md` separates its
additional test-projection slack from actual energy loss and restores the
weaker original signed-defect target as the primary initial-energy route.
No near-saturation or small OWN-relative energy is claimed. The existing
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:293`
`paddedSquare_energy_band_raw` and `:226` `squareResponseFraction_positive`
already supply a strictly positive finite response fraction; another generic
strictness lemma would not supply the missing changing-family estimate.

Nontrivial continuum survival, physical calibration, canonical reflected OS
realization, continuum fields/full QFT, every compact simple group and the
whole Clay theorem remain OPEN. No canonical frontier field changes.

## Verification and reproducibility

Accepted focused checks, actual terminal exit 0, no errors/warnings/sorryAx:

- GNSOrthogonalDualProjection:
  `/tmp/ym-gns-orthogonal-dual-projection-20261003-1.log`, seven gates:
  the two definitions are axiom-free; the five theorems use only
  `{propext, Quot.sound}`. Source SHA256
  `69d58c7ba93b94130143211ed8effc070e390d7dd05f59dfeec97c16a64728b1`;
  log SHA256 `2e06490febba2eb7f9223277cb820742d87132c5930c5db8e93be3ebd04dfab8`.
- BF4DyadicWilsonSquareConnectedDualOverlap:
  `/tmp/ym-square-connected-dual-overlap-20261003-4.log`, eight gates,
  all exactly `{propext, Quot.sound}`. Source SHA256
  `a034f69c83435695baa5666559005a04a0f8ee4db6b459543c31642f6e08c85e`;
  log SHA256 `3356dffe3e6a57d5f21237f61837c5d9550fc71dc848c60088831d2e65067860`.

For each leaf, from the repository root:
`python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 12 --check-worker-limit-gib 20 --status-seconds 300 --log-file /tmp/CHOSEN.log --check lean/YMGap/Continuum/LEAF.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/LEAF.olean`.
Fresh swap/pressure readings at each launch reported zero swap and 76-77%
free memory; the accepted generic and final concrete launches also checked
processes before launch. The second failed concrete launch's sandboxed process
query was denied; immediately after launch an approved query confirmed only
its single monitored compiler. Compilers were serialized, with the 20GiB
worker ceiling and 12GiB OS reserve. No safety interruption occurred.

Concrete attempts 1-3 are NOT proof evidence: quotation precheck, then eager
definitional expansion, then explicit closure of the locally opaque D0
needed correction. Mathematical statements and existing guards were unchanged.
Independent Sol semantic review and source/log QA were used. Root imports
are registration only. No full-root/full-tree build, full axiom audit,
guard or metrics run is claimed; no sorry/axiom/field weakening/CI change.

The canonical ASCII block is unchanged (SHA256
`6f64d1437f38622c455b8d123f001def2a5c459eebf9e785b3e40d117b19a179`),
so it was not reprinted.
