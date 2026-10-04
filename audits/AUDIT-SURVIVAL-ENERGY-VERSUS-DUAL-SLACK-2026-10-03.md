# Survival energy versus dual-test slack

## Scope and outcome

Read-only mathematical/source review at `1f2f567`, followed by this planning
correction. No new Lean theorem, axiom gate or action-specific analytic bound
is claimed. The constructive continuum Yang--Mills/physical mass-gap goal on
R^4 for every compact simple group remains OPEN.

The preceding connected-overlap proof is valid. However, its near-alignment
target must remain OPTIONAL: it controls true energy loss PLUS another
nonnegative loss from the chosen dual test. The primary initial-energy target
remains the weaker original signed-defect estimate. This does not assert a
counterexample for the actual Wilson source or prove that its alignment fails.

## SAME-source algebra separating the two losses

Use the original notation of
`lean/YMGap/Continuum/BF4DyadicWilsonSquareConnectedDualOverlap.lean:86`
`squareSpectatorMeanMismatch` and `:96` `squareConnectedDualMoment`:

    q=V*g_(n+1), psi=f-mu, x=q*psi, t=R*(f-a*mu),
    Z=B(q,q), S=Z*OWNVar, a=w^(12*side),
    D0=Z*D-a*m^2, U=H[q*P(R)*psi^2].

The exact OWN mean mu is from q*P(q), not q*P(R). The original kinetic
diagonal J=G+a*S is pinned by
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedOverlapGain.lean:97`
`paddedSquare_kinetic_signedHeatDefect_pin`. The COMPLETE original energy
identity E=(1-a)*S-G=S-J is
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:129`
`paddedSquare_energy_signedHeatDefect_identity`.

Define, for this source review only,

    H = J*D0-a*Z*U^2.

H>=0 is exactly the inequality in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareConnectedDualOverlap.lean:230`
`paddedSquare_connected_overlap_cleared`. Substitution of E=S-J gives

    S*D0-a*Z*U^2 = E*D0+H.

This displayed algebraic consequence is not a separately added/gated Lean
declaration. The existing `:284`
`paddedSquare_energy_connected_overlap_cleared` gives E*D0+a*Z*U^2<=S*D0.
Consequently near-alignment a*Z*U^2>=(1-epsilon)*S*D0 bounds E*D0+H, not E
alone. Cancelling D0 requires its positivity to be proved; its existing
nonnegativity theorem at `:217` permits zero. No new positivity premise or
inverse is introduced in this review.

The WEAKER direct target is

    G >= (1-a-epsilon)*S,

equivalent by the exact original energy identity to E<=epsilon*S. It has no
dual-test slack or dual inverse. Neither useful target is proved on a justified
changing family. No actual-source theorem establishing H<=C*E*D0 was found in
the searched SignedHeatDefect, SignedOverlapGain, ConnectedDualOverlap or
SpectatorResponse modules; necessity of near-alignment is NOT established.

## Why two retained tests do not automatically pay the missing input

The existing original spectator is constructed in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalSpectator.lean:140`
`spectator`: complementary spatial factors times `erasedTerminal` at `:135`,
which retains the full predecessor input and the rest-block heat. It is not
the endpoint q or its terminal successor.

`lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:138`
`paddedSquare_spectator_kinetic` pins P(R*f)=a*P(R)*f; `:162`
`paddedSquare_spectator_zero` gives H[R*P(R)*f]=0. Neither pin identifies the
q*P(q) OWN law with q*P(R). In particular OWN centering does not erase
the computed mismatch m.

The parallel paper review of span{R,R*f} exposes additional moments
H[q*P(R)] and H[q*P(R)*f]. Optimizing that span is finite Gram algebra, not
a source-specific bound on those moments versus S. No second-test wrapper
or further Gram bundle was added. No useful original-law comparison paying
this mismatch was found in LocalSpectator, SpectatorResponse, SignedOverlapGain
or ConnectedDualOverlap.

## Backward consumers and next causal action

`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`
`completed_reference_ratio` consumes ONE actual finite-depth energy/OWN-variance
bound at all sufficiently late cutoffs, with the original terminal-comparison
factor explicit. Its finite reference estimate is still missing on a justified
changing family. Seek the weaker signed-defect bound, preserving the SAME
source, depth, action, partition and OWN variance; do not add test alignment
as another prerequisite. The alternative consumer remains
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`
`original_window_budget_macro_ratio`, with its complete aggregate signed cost
versus the SAME starting variance still unpaid.

The review also considered expressing positivity/PSD as
`-h*Angular <= normalizedRemainder <= OWNVar-h*Angular`. Without a better
coefficient this is only the existing 0<=E<=S in different notation, not a
new action-specific scaling estimate. Do not treat that re-expression as
paying the analytic input or expand its interface merely to count a proof.

## Evidence boundary

Two Sol mathematical reviews and a Luna source-anchor review were used.
The current definitions and theorem statements were inspected directly.
No Lean source, frontier statement, sorry, axiom or CI setting changed;
no compiler/full-root/tree/audit/guard/metrics run was needed or claimed.
The canonical ASCII block remains unchanged; no chart or paper-list reprint.
